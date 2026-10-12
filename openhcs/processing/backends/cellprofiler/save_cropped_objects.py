"""CellProfiler SaveCroppedObjects: one image file per object."""

from __future__ import annotations

from abc import ABC, abstractmethod
from enum import Enum
from pathlib import PurePosixPath
from typing import TYPE_CHECKING, ClassVar

import numpy as np
from metaclass_registry import AutoRegisterMeta
from metaclass_registry.strategies import EnumKeyedStrategyMixin

from openhcs.core.artifacts.kinds import (
    ImageArtifactType,
    ObjectLabelsArtifactType,
    SpecialArtifactType,
)
from openhcs.core.artifacts.specs import ArtifactSpec, ArtifactSpecCollection
from openhcs.core.materialization import (
    FileBundleOptions,
    MaterializationSpec,
    Output,
)
from openhcs.core.memory.decorators import numpy
from openhcs.core.pipeline.function_contracts import (
    FullStackLabels,
    object_label_input_execution_mode,
    special_inputs,
)
from openhcs.core.processing_contracts import Pure2DContract, Pure3DContract
from openhcs.core.runtime_array_values import RuntimeArrayData
from openhcs.core.runtime_image_values import ImagePayload, ImagePayloadMetadata
from openhcs.core.runtime_object_labels import (
    ObjectLabelValue,
    object_label_dense_array,
)
from openhcs.interop.cellprofiler.module_artifact_declarations import (
    ObjectArtifactInputModule,
)
from openhcs.interop.cellprofiler.module_declarations import CellProfilerModule
from openhcs.interop.cellprofiler.setting_names import (
    SettingNameFamily,
    normalized_symbol_name,
    optional_setting_value,
)
from openhcs.interop.cellprofiler.settings_binder import (
    SettingToKeywordBinding,
    cellprofiler_enum_setting_parser,
    parse_cellprofiler_bool,
)
from openhcs.processing.backends.cellprofiler.morphology import (
    ZStackFunctionVariantModule,
)
from openhcs.processing.backends.cellprofiler.save_images import SaveImagesBitDepth

if TYPE_CHECKING:
    from openhcs.core.function_patterns import FunctionInvocationKey
    from openhcs.core.invocation_artifacts import ArtifactDeclarationStepContext
    from openhcs.interop.cellprofiler.module_settings import BoundModuleSettings
    from openhcs.interop.cellprofiler.parser import ModuleBlock


class CropExport(str, Enum):
    """What SaveCroppedObjects writes for each object (CellProfiler's spelling)."""

    IMAGES = "Images"
    MASKS = "Masks"


class CropFileFormat(str, Enum):
    """File format of each written object (CellProfiler's spelling)."""

    PNG = "png"
    TIFF_8 = "8-bit tiff"
    TIFF_16 = "16-bit tiff"


class CropContent(EnumKeyedStrategyMixin[CropExport], ABC, metaclass=AutoRegisterMeta):
    """The pixels written for one object, per ``CropExport`` member."""

    __enum_member_attr__ = "export"
    export: ClassVar[CropExport | None] = None

    @abstractmethod
    def pixels(self, object_mask: np.ndarray, image: np.ndarray | None) -> np.ndarray:
        """Return the pixels of the object whose pixels ``object_mask`` selects."""


class ObjectMaskContent(CropContent):
    """The object's mask over the whole image; it is not cropped."""

    export = CropExport.MASKS

    def pixels(self, object_mask: np.ndarray, image: np.ndarray | None) -> np.ndarray:
        del image
        return object_mask


class CroppedImageContent(CropContent):
    """The image inside the object's bounding box, zero outside the object."""

    export = CropExport.IMAGES

    def pixels(self, object_mask: np.ndarray, image: np.ndarray | None) -> np.ndarray:
        if image is None:
            raise ValueError(
                "SaveCroppedObjects saving cropped images requires the image to crop."
            )
        if image.ndim == object_mask.ndim + 1:
            # A colour image: every channel is cropped by the same object.
            object_mask = np.repeat(
                object_mask[..., np.newaxis], image.shape[-1], axis=-1
            )
        if image.shape != object_mask.shape:
            raise ValueError(
                "SaveCroppedObjects image to crop has shape "
                f"{image.shape}, its objects have shape {object_mask.shape}."
            )
        occupied = np.nonzero(object_mask)
        box = tuple(
            slice(int(indices.min()), int(indices.max()) + 1) for indices in occupied
        )
        return image[box] * object_mask[box]


class CropFileEncoding(
    EnumKeyedStrategyMixin[CropFileFormat], ABC, metaclass=AutoRegisterMeta
):
    """File suffix and stored bit depth, per ``CropFileFormat`` member."""

    __enum_member_attr__ = "file_format"
    file_format: ClassVar[CropFileFormat | None] = None
    suffix: ClassVar[str]
    bit_depth: ClassVar[SaveImagesBitDepth]
    stores_volumes: ClassVar[bool] = True

    def stored_pixels(self, pixels: np.ndarray, *, volume: bool) -> np.ndarray:
        """Return ``pixels`` at this format's bit depth."""

        if volume and not self.stores_volumes:
            raise ValueError(
                f"SaveCroppedObjects cannot write a 3D object as {self.suffix}; "
                "choose a tiff format."
            )
        return np.asarray(self.bit_depth.convert(ImagePayload.of(pixels)).data)


class PngCropEncoding(CropFileEncoding):
    file_format = CropFileFormat.PNG
    suffix = ".png"
    bit_depth = SaveImagesBitDepth.UINT8
    stores_volumes = False


class Tiff8CropEncoding(CropFileEncoding):
    file_format = CropFileFormat.TIFF_8
    suffix = ".tiff"
    bit_depth = SaveImagesBitDepth.UINT8


class Tiff16CropEncoding(CropFileEncoding):
    file_format = CropFileFormat.TIFF_16
    suffix = ".tiff"
    bit_depth = SaveImagesBitDepth.UINT16


class CropDirectoryChoice(ABC, metaclass=AutoRegisterMeta):
    """A choice of CellProfiler's ``Directory`` setting OpenHCS can write to.

    The setting is spelled ``<choice>|<path>``. Each subclass is one choice,
    registered under CellProfiler's text for it, and returns the directory
    below the step's output folder. A choice with no subclass is refused.
    """

    __registry_key__ = "choice"
    __skip_if_no_key__ = True
    __registry__: ClassVar[dict[str, type[CropDirectoryChoice]]] = {}

    choice: ClassVar[str | None] = None

    @classmethod
    @abstractmethod
    def relative_directory(cls, path: str) -> str | None:
        """Return the directory below the output folder, or None for the folder."""

    @classmethod
    def parse(cls, value: str) -> str | None:
        """Return the relative directory one ``Directory`` setting value names."""

        choice, _, path = value.partition("|")
        choice_type = cls.__registry__.get(choice.strip())
        if choice_type is None:
            raise ValueError(
                f"SaveCroppedObjects 'Directory' choice {choice.strip()!r} is not "
                "supported: OpenHCS writes crops below the step's output folder, "
                f"so only {tuple(cls.__registry__)!r} can be imported."
            )
        return choice_type.relative_directory(path.strip())


class DefaultOutputFolder(CropDirectoryChoice):
    """The output folder itself; CellProfiler ignores any path stored with it."""

    choice = "Default Output Folder"

    @classmethod
    def relative_directory(cls, path: str) -> None:
        del path


class DefaultOutputSubfolder(CropDirectoryChoice):
    """A fixed directory below the output folder."""

    choice = "Default Output Folder sub-folder"

    @classmethod
    def relative_directory(cls, path: str) -> str:
        directory = PurePosixPath(path.replace("\\", "/"))
        if not path or directory.is_absolute() or ".." in directory.parts:
            raise ValueError(
                "SaveCroppedObjects 'Directory' sub-folder must be a path below "
                f"the output folder, got {path!r}."
            )
        if "\\g<" in path or "(?P<" in path:
            raise ValueError(
                "SaveCroppedObjects 'Directory' sub-folder uses metadata tags "
                f"({path!r}), which OpenHCS does not substitute for this module."
            )
        return directory.as_posix()


class SaveCroppedObjectsModule(
    ZStackFunctionVariantModule,
    ObjectArtifactInputModule,
    CellProfilerModule,
):
    """One image file per object, written through file-bundle materialization.

    The step's function returns a mapping of relative file path to pixels and
    declares it as a ``FileBundleOptions`` output, the materialization owner
    the export modules use; the module writes nothing itself. Like SaveImages
    it is an ordinary OpenHCS callable and leaves the image flow untouched.
    A pipeline that processes Z stacks as volumes gets the 3D function, which
    writes one volume per object.

    Carried over from CellProfiler 4.2.8.1, all eight settings:

    - *Images* or *Masks*. An image crop is the object's bounding box with
      pixels outside the object set to zero (a colour image keeps its
      channels). A mask is the size of the whole image, not cropped.
    - File names ``<Objects>_<object number>`` with the prefix image's file
      name (without extension) as an optional prefix; object numbers are the
      label values, so gaps in numbering stay gaps.
    - Nested folders: a folder named after the prefix, or after the objects
      when there is no prefix.
    - ``png`` and ``8-bit tiff`` store 8 bits, ``16-bit tiff`` stores 16;
      intensities are taken on CellProfiler's 0-1 scale first.
    - Directory: the default output folder (a path stored beside that choice
      is ignored, as CellProfiler ignores it) or a fixed sub-folder of it.

    Refused at import: any other directory choice (default input folder,
    ``Elsewhere...``), a sub-folder that is absolute, leaves the output folder
    or contains metadata tags, saving images with no image to crop, and a
    file-name prefix with no prefix image.

    Differences from CellProfiler:

    - Files land below the OpenHCS step's results folder, not CellProfiler's
      default output folder, and are not registered as images of the plate.
    - The prefix is the file name OpenHCS reads the image under, which is the
      plate's normalized name (``A01_s001_w1_z001_t001``) when the plate is
      read through a virtual workspace, not the name of the file on disk.
    - CellProfiler compresses tiffs with zlib level 6; OpenHCS writes them with
      its own tiff settings. Pixel values are the same, file bytes are not.
    - Pixels are converted to 8 or 16 bits by the SaveImages bit-depth
      conversion, which equals CellProfiler's for values in [0, 1].
      CellProfiler refuses floating-point pixels outside [-1, 1]; OpenHCS
      clips them instead.
    - Without a prefix the file names do not depend on the image. When one
      step invocation holds several images (several sites of a well), their
      crops would carry the same names and the step fails saying so;
      CellProfiler overwrites the earlier image's files silently.
    - A png cannot hold a 3D object; the step fails instead of writing one.
    """

    module_name = "SaveCroppedObjects"
    function_name = "save_cropped_objects"
    function_variants = ("save_cropped_objects_3d",)
    export_setting = SettingNameFamily(
        "Do you want to save cropped images or object masks?"
    )
    input_objects_setting = SettingNameFamily("Objects")
    directory_setting = SettingNameFamily("Directory")
    use_filename_setting = SettingNameFamily(
        "Prefix saved crop image name with input image name?"
    )
    filename_image_setting = SettingNameFamily("Select image name to use as a prefix")
    nested_setting = SettingNameFamily("Save output crops in nested folders?")
    file_format_setting = SettingNameFamily("Saved file format")
    image_setting = SettingNameFamily("Image to crop")

    input_objects_binding = SettingToKeywordBinding.input(
        input_objects_setting,
        ObjectLabelsArtifactType,
        runtime_parameter_name="labels",
    )
    image_binding = SettingToKeywordBinding.input(
        image_setting,
        ImageArtifactType,
        runtime_parameter_name="image_to_crop",
    )
    filename_image_binding = SettingToKeywordBinding.input(
        filename_image_setting,
        ImageArtifactType,
        runtime_parameter_name="filename_image",
    )
    setting_bindings = (
        SettingToKeywordBinding(
            export_setting,
            "export",
            cellprofiler_enum_setting_parser(CropExport),
        ),
        input_objects_binding,
        SettingToKeywordBinding(directory_setting, "directory", CropDirectoryChoice.parse),
        SettingToKeywordBinding(
            use_filename_setting, "prefix_with_filename", parse_cellprofiler_bool
        ),
        filename_image_binding,
        SettingToKeywordBinding(nested_setting, "nested_folders", parse_cellprofiler_bool),
        SettingToKeywordBinding(
            file_format_setting,
            "file_format",
            cellprofiler_enum_setting_parser(CropFileFormat),
        ),
        image_binding,
    )

    @classmethod
    def uses_cellprofiler_runtime_adapter(cls) -> bool:
        """The function is an ordinary OpenHCS callable, as SaveImages is."""

        return False

    @classmethod
    def _saves_images(cls, module: ModuleBlock) -> bool:
        return (
            cellprofiler_enum_setting_parser(CropExport)(
                optional_setting_value(module, cls.export_setting)
                or CropExport.IMAGES.value
            )
            is CropExport.IMAGES
        )

    @classmethod
    def _prefixes_with_filename(cls, module: ModuleBlock) -> bool:
        return parse_cellprofiler_bool(
            optional_setting_value(module, cls.use_filename_setting) or "Yes"
        )

    @classmethod
    def validate_pipeline_import(cls, module: ModuleBlock) -> None:
        """Refuse the setting combinations CellProfiler itself cannot run."""

        for wanted, setting, reason in (
            (cls._saves_images(module), cls.image_setting, "saves cropped images"),
            (
                cls._prefixes_with_filename(module),
                cls.filename_image_setting,
                "prefixes file names with an image's file name",
            ),
        ):
            if wanted and (
                normalized_symbol_name(optional_setting_value(module, setting) or "")
                is None
            ):
                raise ValueError(
                    f"SaveCroppedObjects({module.module_num}) {reason} but "
                    f"{setting.canonical!r} names no image."
                )
        CropDirectoryChoice.parse(
            optional_setting_value(module, cls.directory_setting)
            or DefaultOutputFolder.choice
        )

    @classmethod
    def active_artifact_bindings(
        cls,
        module: ModuleBlock | None = None,
        *,
        invocation_key: FunctionInvocationKey | None = None,
    ) -> tuple[SettingToKeywordBinding, ...]:
        """The image to crop and the prefix image are inputs only when used."""

        bindings = super().active_artifact_bindings(
            module, invocation_key=invocation_key
        )
        if module is None:
            return bindings
        unused = {
            binding
            for binding, used in (
                (cls.image_binding, cls._saves_images(module)),
                (cls.filename_image_binding, cls._prefixes_with_filename(module)),
            )
            if not used
        }
        return tuple(binding for binding in bindings if binding not in unused)

    @classmethod
    def postprocess_bound_settings(
        cls, module: ModuleBlock, bound: BoundModuleSettings
    ) -> BoundModuleSettings:
        """Give the function the objects' name, which every file name carries."""

        bound = super().postprocess_bound_settings(module, bound)
        (objects_name,) = cls.artifact_names_for_binding(
            module, cls.input_objects_binding
        )
        return bound.with_kwargs({"objects_name": objects_name})

    @classmethod
    def main_flow_output_specs(
        cls,
        main_flow_candidates: tuple[ArtifactSpec, ...],
    ) -> tuple[ArtifactSpec, ...]:
        """Writing crops leaves the pipeline's image flow as it was."""

        del cls, main_flow_candidates
        return ()

    @classmethod
    def artifact_contract_outputs(
        cls,
        module: ModuleBlock,
        *,
        invocation_key: FunctionInvocationKey,
        step_context: ArtifactDeclarationStepContext,
        artifact_inputs: ArtifactSpecCollection,
    ) -> tuple[ArtifactSpec, ...]:
        """Declare the crop files as one materialized file bundle."""

        del invocation_key, step_context, artifact_inputs
        return (
            ArtifactSpec.output(
                cls.canonical_numbered_module_output_artifact_name(
                    module,
                    artifact_type=SpecialArtifactType,
                    output_position=0,
                ),
                SpecialArtifactType,
                materialization=MaterializationSpec(FileBundleOptions()),
            ),
        )


def _source_file_stem(filename_image: RuntimeArrayData | None) -> str:
    source_path = (
        None
        if filename_image is None
        else ImagePayload.of(
            filename_image
        ).metadata.source_provenance.scalar_source_identity.path
    )
    if source_path is None:
        raise ValueError(
            "SaveCroppedObjects prefixes file names with the input image's file "
            "name, but the prefix image does not come from one source file."
        )
    return PurePosixPath(str(source_path).replace("\\", "/")).stem


def _object_files(
    labels: ObjectLabelValue,
    image_to_crop: RuntimeArrayData | None,
    filename_image: RuntimeArrayData | None,
    *,
    objects_name: str,
    export: CropExport,
    file_format: CropFileFormat,
    directory: str | None,
    prefix_with_filename: bool,
    nested_folders: bool,
) -> dict[str, Output]:
    """Return every object's file, keyed by its path below the output folder."""

    label_data = object_label_dense_array(labels, dtype=np.int32)
    content = CropContent.for_enum_member(export)
    encoding = CropFileEncoding.for_enum_member(file_format)
    # CellProfiler crops intensities on its 0-1 scale, whatever the file stored.
    pixels = (
        None
        if image_to_crop is None
        else np.asarray(
            ImagePayload.of(image_to_crop).normalize_intensity_payload().data
        )
    )
    prefix = f"{_source_file_stem(filename_image)}_" if prefix_with_filename else ""
    folder = PurePosixPath(directory or "")
    if nested_folders:
        folder = folder / (prefix[:-1] if prefix else objects_name)
    files: dict[str, Output] = {}
    for object_number in np.unique(label_data[label_data > 0]):
        path = (
            folder / f"{prefix}{objects_name}_{int(object_number)}{encoding.suffix}"
        ).as_posix()
        stored = encoding.stored_pixels(
            content.pixels(label_data == object_number, pixels),
            volume=label_data.ndim == 3,
        )
        # One object's file is not a plane of the plate, so it carries its own
        # pixel facts and no plate address.
        files[path] = Output(
            path=path,
            content=stored,
            metadata=ImagePayloadMetadata.for_array(stored),
        )
    return files


@numpy(contract=Pure2DContract)
@special_inputs("labels", "image_to_crop", "filename_image")
def save_cropped_objects(
    image: ImagePayload,
    labels: ObjectLabelValue,
    image_to_crop: RuntimeArrayData | None = None,
    filename_image: RuntimeArrayData | None = None,
    *,
    objects_name: str = "Objects",
    export: CropExport = CropExport.IMAGES,
    file_format: CropFileFormat = CropFileFormat.TIFF_8,
    directory: str | None = None,
    prefix_with_filename: bool = True,
    nested_folders: bool = False,
) -> tuple[ImagePayload, dict[str, Output]]:
    """Return one image file per object, keyed by its path below the output folder.

    Args:
        labels: Objects to write, one file per object number.
        image_to_crop: Image the crops are taken from when ``export`` is images.
        filename_image: Image whose source file name prefixes every file name.
        objects_name: Name of the objects, part of every file name.
        export: Whether each file holds the cropped image or the object's mask.
        file_format: File type and bit depth of each file.
        directory: Directory below the step's output folder; None for the folder.
        prefix_with_filename: Whether file names start with the source file name.
        nested_folders: Whether files go into a folder named after the prefix,
            or after the objects when there is no prefix.
    """
    return image, _object_files(
        labels,
        image_to_crop,
        filename_image,
        objects_name=objects_name,
        export=export,
        file_format=file_format,
        directory=directory,
        prefix_with_filename=prefix_with_filename,
        nested_folders=nested_folders,
    )


@numpy(contract=Pure3DContract)
@object_label_input_execution_mode(FullStackLabels)
@special_inputs("labels", "image_to_crop", "filename_image")
def save_cropped_objects_3d(
    image: ImagePayload,
    labels: ObjectLabelValue,
    image_to_crop: RuntimeArrayData | None = None,
    filename_image: RuntimeArrayData | None = None,
    *,
    objects_name: str = "Objects",
    export: CropExport = CropExport.IMAGES,
    file_format: CropFileFormat = CropFileFormat.TIFF_8,
    directory: str | None = None,
    prefix_with_filename: bool = True,
    nested_folders: bool = False,
) -> tuple[ImagePayload, dict[str, Output]]:
    """Return one volume file per 3D object, keyed by its path below the output folder.

    Args:
        labels: Object volume to write, one file per object number.
        image_to_crop: Volume the crops are taken from when ``export`` is images.
        filename_image: Image whose source file name prefixes every file name.
        objects_name: Name of the objects, part of every file name.
        export: Whether each file holds the cropped volume or the object's mask.
        file_format: File type and bit depth of each file; png cannot hold a volume.
        directory: Directory below the step's output folder; None for the folder.
        prefix_with_filename: Whether file names start with the source file name.
        nested_folders: Whether files go into a folder named after the prefix,
            or after the objects when there is no prefix.
    """
    return image, _object_files(
        labels,
        image_to_crop,
        filename_image,
        objects_name=objects_name,
        export=export,
        file_format=file_format,
        directory=directory,
        prefix_with_filename=prefix_with_filename,
        nested_folders=nested_folders,
    )
