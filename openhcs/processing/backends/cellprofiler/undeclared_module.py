"""The step a CellProfiler module becomes when OpenHCS has no declaration for it.

A ``.cppipe`` may name a module OpenHCS does not implement (a lab's plugin, a
built-in that has not been absorbed). The pipeline still imports: the module
becomes one ordinary ``FunctionStep`` that keeps the module's name, revision
and settings as written, is wired into the dataflow so later modules resolve
their inputs, and refuses to compile until its function is replaced.

What the module reads and writes is derived from the pipeline around it, never
from the meaning of its settings:

- an *output* is a name a later module reads that nothing before that reader
  provides and that appears as a setting value of this block (the nearest such
  block before the reader gets it);
- an *input* is a setting value naming an image or objects available before
  this block.

In a pipeline CellProfiler itself accepts, every name a module reads has an
earlier provider, so the derived outputs are exact for the names later modules
use. Outputs nothing later reads are not known and are not declared.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import TYPE_CHECKING, NoReturn

import numpy as np

from openhcs.core.artifacts.kinds import (
    ArtifactType,
    ImageArtifactType,
    ObjectLabelsArtifactType,
)
from openhcs.core.artifacts.plans import ArtifactInputPlan, ArtifactOutputPlan
from openhcs.core.memory.decorators import numpy
from openhcs.core.processing_contracts import FlexibleContract
from openhcs.interop.cellprofiler.module_declarations import CellProfilerModule
from openhcs.interop.cellprofiler.module_settings import BoundModuleSettings
from openhcs.interop.cellprofiler.parser import ModuleBlock, ModuleSetting
from openhcs.interop.cellprofiler.setting_names import (
    setting_names,
    split_symbol_names,
)
from openhcs.interop.cellprofiler.settings_binder import SettingToKeywordBinding

if TYPE_CHECKING:
    from collections.abc import Callable

    from openhcs.core.callable_contract import CallableContract
    from openhcs.core.function_patterns import (
        FunctionInvocationKey,
        NormalizedFunctionItem,
    )
    from openhcs.core.invocation_artifacts import ArtifactDeclarationStepContext


def _names(value: str | tuple[str, ...]) -> tuple[str, ...]:
    """Return artifact names from the scalar-or-tuple form step kwargs carry."""

    return (value,) if isinstance(value, str) else tuple(value)


@numpy(contract=FlexibleContract)
def undeclared_module(
    image: np.ndarray,
    module_name: str = "",
    variable_revision_number: int | None = None,
    settings: tuple[tuple[str, str], ...] = (),
    input_images: str | tuple[str, ...] = (),
    input_objects: str | tuple[str, ...] = (),
    output_images: str | tuple[str, ...] = (),
    output_objects: str | tuple[str, ...] = (),
) -> NoReturn:
    """Stand in for a CellProfiler module that has no OpenHCS implementation.

    The step cannot run. Replace its function with one that produces the
    listed outputs.

    Args:
        module_name: The module's name as written in the CellProfiler pipeline.
        variable_revision_number: The module's settings revision in the pipeline.
        settings: The module's settings as written, in order, as (setting, value).
        input_images: Images available before this module that its settings name.
        input_objects: Objects available before this module that its settings name.
        output_images: Images later modules read that this module's settings name.
        output_objects: Objects later modules read that this module's settings name.
    """

    del image, variable_revision_number, settings, input_images, input_objects
    raise NotImplementedError(
        UndeclaredModule.no_implementation_message(
            module_name,
            output_images=_names(output_images),
            output_objects=_names(output_objects),
        )
    )


@dataclass
class UndeclaredModuleBlock(ModuleBlock):
    """A parsed block whose module has no declaration.

    ``written_settings`` are the block's rows from the file. ``setting_records``
    hold only the artifact rows derived for it, so a written setting can never
    be read as an artifact row, whatever its text.
    """

    written_settings: tuple[tuple[str, str], ...] = ()

    def written_names(self) -> tuple[str, ...]:
        """Return the distinct artifact-name candidates among the written values."""

        return tuple(
            dict.fromkeys(
                name
                for _setting, value in self.written_settings
                for name in split_symbol_names(value)
            )
        )


class UndeclaredModule(CellProfilerModule):
    """Imports any module block whose name has no registered declaration."""

    module_name = "UndeclaredModule"
    function_name = "undeclared_module"
    confidence = 0.0

    input_image_binding = SettingToKeywordBinding.input(
        "Input images",
        ImageArtifactType,
        repeated=True,
    )
    input_object_binding = SettingToKeywordBinding.input(
        "Input objects",
        ObjectLabelsArtifactType,
        repeated=True,
    )
    output_image_binding = SettingToKeywordBinding.output(
        "Output images",
        ImageArtifactType,
        repeated=True,
    )
    output_object_binding = SettingToKeywordBinding.output(
        "Output objects",
        ObjectLabelsArtifactType,
        repeated=True,
    )
    setting_bindings = (
        input_image_binding,
        input_object_binding,
        output_image_binding,
        output_object_binding,
    )

    @classmethod
    def no_implementation_message(
        cls,
        module_name: str,
        *,
        output_images: tuple[str, ...],
        output_objects: tuple[str, ...],
    ) -> str:
        """Say which module cannot run and what its replacement must produce."""

        del cls
        outputs = (
            *(f"image {name!r}" for name in output_images),
            *(f"objects {name!r}" for name in output_objects),
        )
        produced = (
            f"producing {', '.join(outputs)}"
            if outputs
            else "(no later module reads an output of it)"
        )
        return (
            f"CellProfiler module {module_name!r} has no OpenHCS implementation, "
            "so this step cannot run. Replace the step's function with a custom "
            f"function {produced}."
        )

    @classmethod
    def adjacent_blocks_share_step(cls) -> bool:
        """Each block is its own step: adjacent blocks may be different modules."""
        return False

    @classmethod
    def validate_compilation(cls, invocation: NormalizedFunctionItem) -> None:
        """Refuse to compile: nothing implements the module this step stands for."""

        kwargs = invocation.kwargs_dict
        raise ValueError(
            cls.no_implementation_message(
                kwargs.get("module_name", ""),
                output_images=_names(kwargs.get("output_images", ())),
                output_objects=_names(kwargs.get("output_objects", ())),
            )
        )

    @classmethod
    def validate_callable_artifact_abi(
        cls,
        func: Callable[..., NoReturn],
        contract: CallableContract,
    ) -> None:
        """The callable never returns, so it has no return slots to check."""

        del cls, func, contract

    @classmethod
    def invocation_module_blocks(
        cls,
        module: ModuleBlock,
    ) -> tuple[ModuleBlock, ...]:
        """Set the written rows aside; artifact rows are derived, not read."""

        del cls
        return (
            UndeclaredModuleBlock(
                name=module.name,
                module_num=module.module_num,
                enabled=module.enabled,
                metadata=dict(module.metadata),
                cppipe_path=module.cppipe_path,
                written_settings=tuple(
                    (setting.name, setting.value) for setting in module.iter_settings()
                ),
            ),
        )

    @classmethod
    def _undeclared_block(cls, module: ModuleBlock) -> UndeclaredModuleBlock:
        if not isinstance(module, UndeclaredModuleBlock):
            raise TypeError(
                f"{cls.__name__} derives artifact rows only for the block its "
                f"invocation_module_blocks built, got {type(module).__name__}."
            )
        return module

    @classmethod
    def _artifact_rows(
        cls,
        binding: SettingToKeywordBinding,
        names: tuple[str, ...],
    ) -> list[ModuleSetting]:
        del cls
        setting_name = setting_names(binding.setting_name)[0]
        return [ModuleSetting(setting_name, name) for name in names]

    @classmethod
    def block_in_artifact_context(
        cls,
        module: ModuleBlock,
        *,
        step_context: ArtifactDeclarationStepContext,
    ) -> ModuleBlock:
        """Read every image or objects available here that a written value names."""

        block = cls._undeclared_block(module)
        rows: list[ModuleSetting] = []
        for binding in cls.declared_artifact_bindings(plan_type=ArtifactInputPlan):
            rows.extend(
                cls._artifact_rows(
                    binding,
                    tuple(
                        name
                        for name in block.written_names()
                        if cls.available_artifact_input_specs(
                            name,
                            binding.require_artifact_type(),
                            step_context=step_context,
                        )
                    ),
                )
            )
        for binding in cls.declared_artifact_bindings(plan_type=ArtifactOutputPlan):
            rows.extend(
                cls._artifact_rows(
                    binding,
                    cls.artifact_names_for_binding(block, binding),
                )
            )
        return replace(block, setting_records=rows)

    @classmethod
    def block_providing_artifact(
        cls,
        module: ModuleBlock,
        *,
        name: str,
        artifact_type: type[ArtifactType],
    ) -> ModuleBlock | None:
        """Provide an artifact a later module reads when a written value names it."""

        block = cls._undeclared_block(module)
        if name not in block.written_names():
            return None
        for binding in cls.declared_artifact_bindings(
            plan_type=ArtifactOutputPlan,
            artifact_type=artifact_type,
        ):
            if name in cls.artifact_names_for_binding(block, binding):
                return None
            return replace(
                block,
                setting_records=[
                    *block.setting_records,
                    *cls._artifact_rows(binding, (name,)),
                ],
            )
        return None

    @classmethod
    def postprocess_bound_settings(
        cls,
        module: ModuleBlock,
        bound: BoundModuleSettings,
    ) -> BoundModuleSettings:
        """Carry the module's written name, revision and settings as step kwargs."""

        block = cls._undeclared_block(module)
        return bound.with_kwargs(
            {
                "module_name": block.name,
                "variable_revision_number": block.variable_revision_number,
                "settings": block.written_settings,
            }
        )

    @classmethod
    def artifact_input_bindings_for_reconstruction(
        cls,
        module: ModuleBlock,
        *,
        invocation_key: FunctionInvocationKey,
        step_context: ArtifactDeclarationStepContext,
    ) -> tuple[SettingToKeywordBinding, ...]:
        """Inputs are exactly the named ones; the main flow supplies no default."""

        del cls, module, invocation_key, step_context
        return ()

    @classmethod
    def derives_missing_output_identity(
        cls,
        binding: SettingToKeywordBinding,
    ) -> bool:
        """Outputs are exactly the named ones; none is invented for a binding."""

        del cls, binding
        return False
