"""Shared component semantics for streaming viewer backends."""

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import Callable, Mapping, Sequence
from dataclasses import dataclass, field
from enum import Enum
from itertools import product
from typing import ClassVar, Generic, TypeAlias, TypeVar

from metaclass_registry import AutoRegisterMeta, LazyDiscoveryDict, RegistryConfig
from polystore.streaming_constants import StreamingDataType
from polystore.streaming.receivers.core.metadata_presentation import (
    ComponentMetadataPresentationABC,
)
from zmqruntime.viewer_protocol import (
    ViewerBatchDisplayPayload,
    ViewerBatchContextWireField,
    ViewerBatchMessageType,
    ViewerBatchWireField,
    ViewerComponentMode,
    ViewerDisplayConfigWireField,
    ViewerWireMapping,
    ViewerWireValue,
    viewer_component_mode_value,
)
from polystore.streaming.viewer_transport import ViewerDisplayConfigABC

from openhcs.constants.constants import AllComponents
from openhcs.runtime.viewer_protocol import ViewerComponentValueOrdering

ComponentValue: TypeAlias = str | int | float | bool | tuple | None
ComponentWireValue: TypeAlias = ComponentValue | Sequence[ComponentValue]
ComponentMap: TypeAlias = dict[str, ComponentValue]
ComponentValues: TypeAlias = dict[str, list[ComponentValue]]
ComponentCoordinate: TypeAlias = tuple[ComponentValue, ...]
ComponentDomainKey: TypeAlias = str | tuple[str, ...] | tuple[str, tuple[str, ...]]
ComponentModeMap: TypeAlias = dict[str, str]
DisplayModeValue: TypeAlias = str | Enum
DisplayComponentName: TypeAlias = str | Enum
DisplayConfigMappingValue: TypeAlias = (
    Mapping[str, DisplayModeValue] | Sequence[DisplayComponentName]
)
ComponentMetadataItems: TypeAlias = Sequence[Mapping[str, ComponentValue] | None]
ComponentAxisValues: TypeAlias = Mapping[str, Sequence[ComponentValue]]
ComponentNameMetadataWireMapping: TypeAlias = Mapping[
    str,
    Mapping[ComponentWireValue, ComponentWireValue],
]
ViewerBatchField: TypeAlias = ViewerBatchWireField | ViewerBatchContextWireField
DisplayConfigT = TypeVar("DisplayConfigT")
WindowProjectionProviderT = TypeVar("WindowProjectionProviderT")
HandlerRequestT = TypeVar("HandlerRequestT")
HandlerT = TypeVar("HandlerT", bound="ViewerStreamingDataTypeHandler")


class ViewerStreamingDataTypeHandlerMeta(AutoRegisterMeta):
    """Create one streaming-data-type registry for each concrete viewer family."""

    REGISTRY_KEY = "streaming_data_type"
    FAMILY_ROOT_MARKER = "__viewer_streaming_data_type_template__"

    def __new__(mcs, name: str, bases: tuple[type, ...], attrs: dict):
        starts_backend_family = any(
            mcs.FAMILY_ROOT_MARKER in base.__dict__
            and base.__dict__[mcs.FAMILY_ROOT_MARKER] is True
            for base in bases
        )
        if starts_backend_family:
            registry = LazyDiscoveryDict()
            attrs["__registry__"] = registry
            attrs["__registry_key__"] = mcs.REGISTRY_KEY
            attrs["__skip_if_no_key__"] = True
            return super().__new__(
                mcs,
                name,
                bases,
                attrs,
                registry_config=RegistryConfig(
                    registry_dict=registry,
                    key_attribute=mcs.REGISTRY_KEY,
                    skip_if_no_key=True,
                    registry_name=f"{name} streaming data type",
                ),
            )
        return super().__new__(mcs, name, bases, attrs)


class ViewerComponentSemanticRole(Enum):
    """Semantic roles that viewer backends may request from component axes."""

    COLOR = "color"


class ViewerStreamingDataTypeHandler(
    ABC,
    Generic[HandlerRequestT],
    metaclass=ViewerStreamingDataTypeHandlerMeta,
):
    """Template for viewer handlers registered by streaming payload type."""

    __viewer_streaming_data_type_template__: ClassVar[bool] = True
    __registry__: ClassVar[
        Mapping[StreamingDataType, type["ViewerStreamingDataTypeHandler"]]
    ]
    streaming_data_type: ClassVar[StreamingDataType | None] = None

    @classmethod
    def registered_data_types(cls) -> tuple[StreamingDataType, ...]:
        return tuple(cls.__registry__)

    @classmethod
    def for_data_type(
        cls: type[HandlerT],
        payload_stream_data_type: StreamingDataType,
    ) -> HandlerT:
        if payload_stream_data_type not in cls.__registry__:
            raise ValueError(
                f"No {cls.__name__} registered for type {payload_stream_data_type!r}."
            )
        handler_type = cls.__registry__[payload_stream_data_type]
        return handler_type()

    @abstractmethod
    def handle(self, request: HandlerRequestT) -> None:
        """Handle one typed streaming payload batch."""


@dataclass(frozen=True, slots=True)
class ViewerDisplayConfigInput(ABC, metaclass=AutoRegisterMeta):
    """Nominal input adapter for viewer display configs."""

    __registry_key__ = "DISPLAY_CONFIG_INPUT_KIND"
    __skip_if_no_key__ = True
    DISPLAY_CONFIG_INPUT_KIND: ClassVar[str | None] = None

    @abstractmethod
    def layout(self) -> "ViewerComponentLayout":
        """Return a normalized component layout."""


@dataclass(frozen=True, slots=True)
class ViewerMappingDisplayConfigInput(ViewerDisplayConfigInput):
    """Mapping-backed viewer display config input."""

    DISPLAY_CONFIG_INPUT_KIND = "mapping"
    mapping_display_config: Mapping[str, DisplayConfigMappingValue]

    def layout(self) -> "ViewerComponentLayout":
        return ViewerComponentLayoutMappingParser.layout(self.mapping_display_config)


@dataclass(frozen=True, slots=True)
class ViewerObjectDisplayConfigInput(ViewerDisplayConfigInput):
    """Object-backed viewer display config input."""

    DISPLAY_CONFIG_INPUT_KIND = "object"
    object_display_config: ViewerDisplayConfigABC

    def layout(self) -> "ViewerComponentLayout":
        return ViewerComponentLayout.from_parts(
            component_modes=self.object_display_config.component_modes(),
            component_order=self.object_display_config.COMPONENT_ORDER,
        )


class ViewerComponentAddress(ABC):
    """Minimal address contract for component-indexed stream items."""

    @property
    @abstractmethod
    def components(self) -> ComponentMap:
        """Return component metadata for the addressed payload."""


class ViewerComponentAddressedItem(ABC):
    """Minimal item contract for component-indexed stream payloads."""

    @property
    @abstractmethod
    def address(self) -> ViewerComponentAddress:
        """Return the component-addressed payload identity."""


class ViewerComponentLayoutMappingParser:
    """Validate mapping-style display configs before layout construction."""

    @classmethod
    def layout(
        cls,
        mapping_display_config: Mapping[str, DisplayConfigMappingValue],
    ) -> "ViewerComponentLayout":
        component_modes = cls._required_value(
            mapping_display_config,
            ViewerDisplayConfigWireField.COMPONENT_MODES,
            Mapping,
            "mapping",
        )
        component_order = cls._required_value(
            mapping_display_config,
            ViewerDisplayConfigWireField.COMPONENT_ORDER,
            Sequence,
            "sequence",
        )
        if isinstance(component_order, str):
            raise TypeError("display_config['component_order'] must be a sequence.")
        return ViewerComponentLayout.from_parts(
            component_modes=component_modes,
            component_order=component_order,
        )

    @staticmethod
    def _required_value(
        mapping_display_config: Mapping[str, DisplayConfigMappingValue],
        field_name: ViewerDisplayConfigWireField,
        expected_type: type | tuple[type, ...],
        expected_name: str,
    ) -> DisplayConfigMappingValue:
        value = mapping_display_config[field_name.value]
        if not isinstance(value, expected_type):
            raise TypeError(
                f"display_config[{field_name.value!r}] must be a {expected_name}."
            )
        return value


@dataclass(frozen=True, slots=True)
class ViewerComponentLayout(ViewerBatchDisplayPayload):
    """Normalized component-mode layout shared by viewer receivers."""

    @classmethod
    def from_parts(
        cls,
        *,
        component_modes: Mapping[str, DisplayModeValue],
        component_order: Sequence[DisplayComponentName],
    ) -> "ViewerComponentLayout":
        order = tuple(str(component) for component in component_order)
        modes = {
            component: cls._mode_value(component_modes[component])
            for component in order
        }
        return cls(component_modes=modes, component_order=order)

    @staticmethod
    def _mode_value(mode: DisplayModeValue) -> str:
        if isinstance(mode, Enum):
            return str(mode.value)
        return str(mode)

    def group_window_sources(self, sources):
        from polystore.streaming.receivers.core import group_items_by_component_modes

        return group_items_by_component_modes(
            sources,
            display_layout=self,
        )

    def group_window_payloads(
        self, payloads: Sequence[Mapping[str, ComponentWireValue]]
    ):
        from polystore.streaming.receivers.core import WindowProjectionSource

        return self.group_window_sources(
            WindowProjectionSource.from_wire_payloads(payloads)
        )

    def group_window_payload_providers(
        self,
        items: Sequence[WindowProjectionProviderT],
    ):
        from polystore.streaming.receivers.core import WindowProjectionSource

        return self.group_window_sources(
            WindowProjectionSource.from_payload_providers(items)
        )


@dataclass(slots=True)
class ViewerComponentMetadataNormalizer:
    """Normalize component metadata before viewer coordinate indexing."""

    def normalize(self, components: ComponentMap) -> ComponentMap:
        return {
            component: self.normalize_value(component, value)
            for component, value in components.items()
        }

    def normalize_value(self, component: str, value: ComponentValue) -> ComponentValue:
        component_identity = AllComponents.from_value(component)
        if component_identity is None or not component_identity.is_variable_axis():
            return value
        if isinstance(value, str):
            stripped = value.strip()
            if stripped and stripped.lstrip("+-").isdigit():
                return int(stripped)
        return value


@dataclass(frozen=True, slots=True)
class ViewerComponentValueDomainEntry:
    """Declared observed values for one component in a viewer stream batch."""

    component: str
    values: tuple[ComponentValue, ...]

    @classmethod
    def from_values(
        cls,
        component: str,
        values: Sequence[ComponentValue],
    ) -> "ViewerComponentValueDomainEntry":
        unique_values = sorted(set(values), key=ViewerComponentValueOrdering.key)
        return cls(component=component, values=tuple(unique_values))

    @classmethod
    def from_declared_values(
        cls, component: str, values: Sequence[ComponentValue]
    ) -> "ViewerComponentValueDomainEntry":
        """Preserve pixel-plane order, refusing ambiguous coordinate assignments."""
        ordered_values = tuple(values)
        if len(set(ordered_values)) != len(ordered_values):
            raise ValueError(
                "Declared plane coordinates must be unique after normalization."
            )
        return cls(component=component, values=ordered_values)


@dataclass(frozen=True, slots=True)
class ViewerComponentValueDomainPayload:
    """Batch-level component value domain shared by viewer receivers."""

    entries: tuple[ViewerComponentValueDomainEntry, ...]

    @classmethod
    def empty(cls) -> "ViewerComponentValueDomainPayload":
        return cls(entries=())

    @classmethod
    def from_component_metadata(
        cls,
        *,
        component_layout: ViewerComponentLayout,
        metadata_items: Sequence[Mapping[str, ComponentValue] | None],
        normalizer: ViewerComponentMetadataNormalizer | None = None,
    ) -> "ViewerComponentValueDomainPayload":
        if normalizer is None:
            normalizer = ViewerComponentMetadataNormalizer()
        values_by_component: dict[str, list[ComponentValue]] = {
            component: [] for component in component_layout.component_order
        }
        for metadata in metadata_items:
            if metadata is None:
                continue
            normalized_metadata = normalizer.normalize(dict(metadata))
            for component in component_layout.component_order:
                if component in normalized_metadata:
                    values_by_component[component].append(
                        normalized_metadata[component]
                    )
        return cls(
            entries=tuple(
                ViewerComponentValueDomainEntry.from_values(component, values)
                for component, values in values_by_component.items()
                if values
            )
        )

    @classmethod
    def from_wire_mapping(
        cls,
        payload: Mapping[str, Sequence[ComponentWireValue]],
        *,
        context: str,
    ) -> "ViewerComponentValueDomainPayload":
        """Project observed membership with its established sort/dedup contract."""
        return cls(
            tuple(
                ViewerComponentValueDomainEntry.from_values(
                    entry.component, entry.values
                )
                for entry in cls._wire_entries(payload, context=context)
            )
        )

    @classmethod
    def from_ordered_wire_mapping(
        cls,
        payload: Mapping[str, Sequence[ComponentWireValue]],
        *,
        context: str,
    ) -> "ViewerComponentValueDomainPayload":
        """Decode an explicitly ordered pixel-plane coordinate declaration."""
        return cls(
            tuple(
                ViewerComponentValueDomainEntry.from_declared_values(
                    entry.component, entry.values
                )
                for entry in cls._wire_entries(payload, context=context)
            )
        )

    @classmethod
    def _wire_entries(
        cls,
        payload: Mapping[str, Sequence[ComponentWireValue]],
        *,
        context: str,
    ) -> tuple[ViewerComponentValueDomainEntry, ...]:
        """Parse and normalize external coordinates once for either projection."""
        normalizer = ViewerComponentMetadataNormalizer()
        entries = []
        for component, raw_values in payload.items():
            if isinstance(raw_values, str) or not isinstance(raw_values, Sequence):
                raise TypeError(
                    f"{context} component domain for {component!r} must be a sequence."
                )
            component_name = str(component)
            entries.append(
                ViewerComponentValueDomainEntry(
                    component_name,
                    tuple(
                        normalizer.normalize_value(
                            component_name,
                            ViewerComponentValueParser.parse(
                                value,
                                context=f"{context} component {component!r}",
                            ),
                        )
                        for value in raw_values
                    ),
                )
            )
        return tuple(entries)

    def component_values(self) -> ComponentValues:
        return {entry.component: list(entry.values) for entry in self.entries}

    def required_component_values(self, components: Sequence[str]) -> ComponentValues:
        values = self.component_values()
        missing = tuple(
            component for component in components if component not in values
        )
        if missing:
            raise ValueError(
                "Declared component value domain missing required component(s): "
                f"{missing!r}."
            )
        return {component: list(values[component]) for component in components}

    def observed_cardinality(self, component: str) -> int:
        values = self.component_values()
        if component not in values:
            return 0
        return len(values[component])

    def component_value_counts(
        self,
        component_order: Sequence[str],
    ) -> tuple[tuple[str, int], ...]:
        return tuple(
            (component, self.observed_cardinality(component))
            for component in component_order
        )

    def to_wire_mapping(self) -> dict[str, list[ComponentValue]]:
        return {entry.component: list(entry.values) for entry in self.entries}

    def __bool__(self) -> bool:
        return bool(self.entries)


class ViewerComponentValueParser:
    """Parse JSON/wire component values into OpenHCS component values."""

    @staticmethod
    def parse(value: ComponentWireValue, *, context: str) -> ComponentValue:
        if isinstance(value, (str, int, float, bool)) or value is None:
            return value
        if isinstance(value, tuple):
            return value
        if isinstance(value, Sequence):
            return tuple(value)
        raise TypeError(
            f"{context} component value must be scalar or tuple-like, "
            f"got {type(value).__name__}"
        )


class ViewerComponentMetadataPayload:
    """Parse component metadata mappings into canonical viewer component values."""

    @classmethod
    def component_map(
        cls,
        payload: ViewerWireMapping,
        *,
        context: str,
    ) -> ComponentMap:
        return {
            str(component): ViewerComponentValueParser.parse(value, context=context)
            for component, value in payload.items()
        }


@dataclass(frozen=True, slots=True)
class ViewerBatchPayloadFields:
    """Fail-loud typed access to one viewer batch wire payload."""

    payload: ViewerWireMapping
    context: str

    def required_value(self, field: ViewerBatchField) -> ViewerWireValue:
        if field.value not in self.payload:
            raise ValueError(f"{self.context} missing required field: {field.value!r}")
        return self.payload[field.value]

    def required_mapping(self, field: ViewerBatchField) -> ViewerWireMapping:
        value = self.required_value(field)
        if not isinstance(value, Mapping):
            raise TypeError(f"{self.context} field {field.value!r} must be a mapping.")
        return value

    def optional_mapping(self, field: ViewerBatchField) -> ViewerWireMapping:
        if field.value not in self.payload:
            return {}
        value = self.payload[field.value]
        if not isinstance(value, Mapping):
            raise TypeError(f"{self.context} field {field.value!r} must be a mapping.")
        return value

    def required_sequence(self, field: ViewerBatchField) -> Sequence[ViewerWireValue]:
        value = self.required_value(field)
        if isinstance(value, str) or not isinstance(value, Sequence):
            raise TypeError(f"{self.context} field {field.value!r} must be a sequence.")
        return value

    def required_mapping_items(
        self,
        field: ViewerBatchField,
    ) -> list[ViewerWireMapping]:
        items = []
        for index, item in enumerate(self.required_sequence(field)):
            if not isinstance(item, Mapping):
                raise TypeError(
                    f"{self.context} field {field.value!r} item {index} must be a mapping."
                )
            items.append(item)
        return items

    def required_optional_string(self, field: ViewerBatchField) -> str | None:
        value = self.required_value(field)
        if value is None:
            return None
        if not isinstance(value, str):
            raise TypeError(
                f"{self.context} field {field.value!r} must be a string or None."
            )
        return value

    def message_type(self) -> ViewerBatchMessageType:
        return ViewerBatchMessageType(
            str(self.required_value(ViewerBatchWireField.TYPE))
        )

    def require_batch_message(self) -> None:
        message_type = self.message_type()
        if message_type is not ViewerBatchMessageType.BATCH:
            raise ValueError(
                f"{self.context} must be a batch message, got {message_type.value!r}."
            )

    def require_fields(self, fields: Sequence[ViewerBatchField]) -> None:
        missing = tuple(
            field.value for field in fields if field.value not in self.payload
        )
        if missing:
            raise ValueError(f"{self.context} missing required fields: {missing!r}.")

    def required_component_names_metadata(
        self,
        *,
        context: str,
    ) -> ViewerComponentNameMetadata:
        return ViewerComponentNameMetadata.from_wire_mapping(
            self.required_mapping(ViewerBatchWireField.COMPONENT_NAMES_METADATA),
            context=context,
        )

    def optional_component_names_metadata(
        self,
        *,
        context: str,
    ) -> ViewerComponentNameMetadata:
        return ViewerComponentNameMetadata.from_wire_mapping(
            self.optional_mapping(ViewerBatchWireField.COMPONENT_NAMES_METADATA),
            context=context,
        )

    def component_value_domain(
        self,
        *,
        context: str,
    ) -> ViewerComponentValueDomainPayload:
        return ViewerComponentValueDomainPayload.from_wire_mapping(
            self.required_mapping(ViewerBatchWireField.COMPONENT_VALUE_DOMAIN),
            context=context,
        )

    def component_axis_semantics(
        self,
        display_config: ViewerDisplayConfigInput,
        *,
        context: str,
    ) -> "ViewerComponentAxisSemantics":
        return ViewerComponentAxisSemanticsAuthority.from_display_config(
            display_config,
            self.component_value_domain(context=context),
        )


@dataclass(slots=True)
class ViewerComponentValueNameStore:
    """Display names for values of one component."""

    names_by_value: dict[str, ComponentValue] = field(default_factory=dict)

    @classmethod
    def from_mapping(
        cls,
        value_names: Mapping[ComponentWireValue, ComponentWireValue],
        *,
        context: str,
    ) -> "ViewerComponentValueNameStore":
        store = cls()
        store.merge_mapping(value_names, context=context)
        return store

    def merge_mapping(
        self,
        value_names: Mapping[ComponentWireValue, ComponentWireValue],
        *,
        context: str,
    ) -> None:
        for value_key, display_name in value_names.items():
            self.names_by_value[str(value_key)] = ViewerComponentValueParser.parse(
                display_name,
                context=context,
            )

    def merge_store(self, value_names: "ViewerComponentValueNameStore") -> None:
        self.names_by_value.update(value_names.names_by_value)

    def normalized_values(
        self,
        component: str,
        normalizer: ViewerComponentMetadataNormalizer,
    ) -> tuple[ComponentValue, ...]:
        return tuple(
            normalizer.normalize_value(component, value_key)
            for value_key in self.names_by_value
        )

    def display_name(self, value: ComponentValue) -> ComponentValue:
        return self.names_by_value.get(str(value))

    def to_wire_mapping(self) -> dict[str, ComponentValue]:
        return dict(self.names_by_value)


@dataclass(slots=True)
class ViewerComponentNameMetadataStore:
    """Mutable storage for component-value display names."""

    values: dict[str, ViewerComponentValueNameStore] = field(default_factory=dict)

    def merge_mapping(
        self,
        incoming: ComponentNameMetadataWireMapping,
        *,
        context: str,
    ) -> None:
        for component, value_names in incoming.items():
            if not isinstance(value_names, Mapping):
                raise TypeError(
                    f"Component-name metadata entry for {component!r} must be a mapping."
                )
            component_key = str(component)
            if component_key not in self.values:
                self.values[component_key] = ViewerComponentValueNameStore()
            self.values[component_key].merge_mapping(
                value_names,
                context=context,
            )

    def merge_store(self, incoming: "ViewerComponentNameMetadataStore") -> None:
        for component, value_names in incoming.values.items():
            if component not in self.values:
                self.values[component] = ViewerComponentValueNameStore()
            self.values[component].merge_store(value_names)

    def clear(self) -> None:
        self.values.clear()

    def normalized_values(
        self,
        component: str,
        normalizer: ViewerComponentMetadataNormalizer,
    ) -> tuple[ComponentValue, ...]:
        if component not in self.values:
            return ()
        return self.values[component].normalized_values(component, normalizer)

    def display_name(
        self,
        component: str,
        value: ComponentValue,
    ) -> ComponentValue:
        if component not in self.values:
            return None
        return self.values[component].display_name(value)

    def __bool__(self) -> bool:
        return bool(self.values)

    def __contains__(self, component: str) -> bool:
        return component in self.values


@dataclass(frozen=True, kw_only=True)
class ViewerComponentNameMetadata(ComponentMetadataPresentationABC[ComponentValue]):
    """Component-value display names shared by viewer receivers."""

    ABBREVIATIONS: ClassVar[Mapping[str, str]] = {
        AllComponents.CHANNEL.value: "Ch",
        AllComponents.Z_INDEX.value: "Z",
        AllComponents.TIMEPOINT.value: "T",
        AllComponents.SITE.value: "Site",
        AllComponents.WELL.value: "Well",
    }
    METADATA_FORMATTERS: ClassVar[
        Mapping[str, Callable[[ComponentValue, ComponentValue], str]]
    ] = {
        AllComponents.CHANNEL.value: lambda value, name: f"Ch{value}: {name}",
        AllComponents.WELL.value: lambda _value, name: str(name),
    }

    store: ViewerComponentNameMetadataStore = field(
        default_factory=ViewerComponentNameMetadataStore
    )

    @classmethod
    def empty(cls) -> "ViewerComponentNameMetadata":
        return cls()

    @classmethod
    def from_wire_mapping(
        cls,
        payload: ComponentNameMetadataWireMapping,
        *,
        context: str,
    ) -> "ViewerComponentNameMetadata":
        metadata = cls.empty()
        metadata.store.merge_mapping(
            payload,
            context=context,
        )
        return metadata

    def merge(self, incoming: "ViewerComponentNameMetadata") -> None:
        self.store.merge_store(incoming.store)

    def clear(self) -> None:
        self.store.clear()

    def to_wire_mapping(self) -> dict[str, dict[str, ComponentValue]]:
        return {
            component: value_names.to_wire_mapping()
            for component, value_names in self.store.values.items()
        }

    def display_name(self, component: str, value: ComponentValue) -> str | None:
        name = self.store.display_name(component, value)
        if name is None or str(name).lower() == "none":
            return None
        return str(name)

    def abbreviation(self, component: str) -> str:
        if component in self.ABBREVIATIONS:
            return self.ABBREVIATIONS[component]
        return component

    def named_axis_label(self, component: str, value: ComponentValue, name: str) -> str:
        formatter = self.METADATA_FORMATTERS.get(component)
        if formatter is not None:
            return formatter(value, name)
        return f"{component.title()} {value}: {name}"

    def compact_tuple_labels(
        self,
        components: Sequence[str],
        values: Sequence[ComponentValue],
        *,
        context: str,
    ) -> list[str]:
        labels = []
        for component_index, component in enumerate(components):
            try:
                value = values[component_index]
            except IndexError as error:
                raise ValueError(
                    f"{context} value {tuple(values)!r} does not include "
                    f"component {component!r}."
                ) from error
            labels.append(self.compact_label(component, value))
        return labels

    def compact_tuple_label(
        self,
        components: Sequence[str],
        values: Sequence[ComponentValue],
        *,
        default: str,
        context: str,
    ) -> str:
        labels = self.compact_tuple_labels(
            components,
            values,
            context=context,
        )
        if labels:
            return " | ".join(labels)
        return default

    def __bool__(self) -> bool:
        return bool(self.store)

    def __contains__(self, component: str) -> bool:
        return component in self.store

    def __iter__(self):
        return iter(self.store.values)


@dataclass(frozen=True, slots=True)
class ViewerComponentAxisSemantics(ViewerComponentValueDomainPayload):
    """Shared component-axis layout plus declared value-domain carrier."""

    layout: ViewerComponentLayout

    @property
    def component_order(self) -> tuple[str, ...]:
        return self.layout.component_order

    @property
    def component_modes(self) -> ComponentModeMap:
        return self.layout.component_modes

    def role_component_for_mode(
        self,
        *,
        role: ViewerComponentSemanticRole,
        mode: DisplayModeValue,
    ) -> str | None:
        mode_value = viewer_component_mode_value(mode)
        for component in self.layout.component_order:
            if self.layout.component_modes[component] != mode_value:
                continue
            component_identity = AllComponents.from_value(component)
            if component_identity is not None and self.component_has_role(
                component_identity, role
            ):
                return component
        return None

    @staticmethod
    def component_has_role(
        component: AllComponents,
        role: ViewerComponentSemanticRole,
    ) -> bool:
        if role is ViewerComponentSemanticRole.COLOR:
            return component.is_default_group_by_axis()
        raise ValueError(f"No component role mapping for {role!r}.")


class ViewerComponentAxisSemanticsAuthority:
    """Build component-axis semantics from external config/domain inputs."""

    @staticmethod
    def from_display_config(
        display_config: ViewerDisplayConfigInput,
        value_domain: ViewerComponentValueDomainPayload,
    ) -> ViewerComponentAxisSemantics:
        return ViewerComponentAxisSemantics(
            entries=value_domain.entries,
            layout=display_config.layout(),
        )

    @staticmethod
    def from_display_config_and_metadata(
        *,
        display_config: ViewerDisplayConfigInput,
        metadata_items: ComponentMetadataItems,
    ) -> ViewerComponentAxisSemantics:
        layout = display_config.layout()
        return ViewerComponentAxisSemantics(
            entries=ViewerComponentValueDomainPayload.from_component_metadata(
                component_layout=layout,
                metadata_items=metadata_items,
            ).entries,
            layout=layout,
        )

    @staticmethod
    def empty() -> ViewerComponentAxisSemantics:
        return ViewerComponentAxisSemantics(
            entries=(),
            layout=ViewerComponentLayout.from_parts(
                component_modes={},
                component_order=(),
            ),
        )


@dataclass(frozen=True, slots=True, kw_only=True)
class ViewerDisplayBatchContext(
    ViewerComponentAxisSemantics,
    ViewerComponentNameMetadata,
    Generic[DisplayConfigT],
):
    """Shared viewer batch context for display config and component domains."""

    viewer_display_config: DisplayConfigT


@dataclass(slots=True)
class ViewerComponentValueDomain:
    """Own observed and declared values for one routed component domain."""

    axis_components: tuple[str, ...]
    observed_values: dict[str, set[ComponentValue]]
    declared_values: dict[str, set[ComponentValue]]

    @classmethod
    def for_axes(
        cls,
        axis_components: Sequence[str],
    ) -> "ViewerComponentValueDomain":
        axes = tuple(axis_components)
        return cls(
            axis_components=axes,
            observed_values={component: set() for component in axes},
            declared_values={component: set() for component in axes},
        )

    def replace_observed(
        self,
        layer_items: Sequence[ViewerComponentAddressedItem],
    ) -> None:
        self.observed_values = {
            component: set() for component in self.axis_components
        }
        for item in layer_items:
            components = item.address.components
            for component in self.axis_components:
                if component in components:
                    self.observed_values[component].add(components[component])

    def observe_component_values(
        self,
        component_values: ComponentValues,
    ) -> None:
        for component, values in component_values.items():
            if component not in self.observed_values:
                raise ValueError(
                    "Component value domain cannot observe undeclared component "
                    f"{component!r}; axes={self.axis_components!r}."
                )
            self.observed_values[component].update(values)

    def declare(
        self,
        component_values: ComponentValues,
    ) -> None:
        missing = tuple(
            component
            for component in self.axis_components
            if component not in component_values
        )
        if missing:
            raise ValueError(
                "Declared component value domain is missing route axis component(s) "
                f"{missing!r}."
            )
        self.declared_values = {
            component: set(component_values[component])
            for component in self.axis_components
        }

    def observed(self) -> ComponentValues:
        return {
            component: sorted(values, key=ViewerComponentValueOrdering.key)
            for component, values in self.observed_values.items()
        }

    def coordinate_values(self, component: str) -> set[ComponentValue]:
        if component not in self.observed_values:
            return set()
        return self.observed_values[component] | self.declared_values[component]


@dataclass(frozen=True, slots=True)
class ViewerComponentValueDomainView:
    """Named view over component values used by layer-axis projection."""

    values: ComponentValues
    domain_name: str

    def required_values(self, component: str) -> list[ComponentValue]:
        if component not in self.values:
            raise ValueError(
                f"{self.domain_name} component domain missing '{component}'."
            )
        component_values = self.values[component]
        if len(component_values) == 0:
            raise ValueError(
                f"{self.domain_name} component domain for '{component}' is empty; "
                f"domain={self.values!r}."
            )
        return component_values

    def require_contains(
        self,
        component: str,
        route_values: Sequence[ComponentValue],
        *,
        owner: str,
    ) -> None:
        domain_values = self.required_values(component)
        missing = tuple(value for value in route_values if value not in domain_values)
        if missing:
            raise ValueError(
                f"{owner} component domain for '{component}' does not contain "
                f"route value(s) {missing!r}; domain={domain_values!r}."
            )

    def has_multiple_values(self, component: str) -> bool:
        if component not in self.values:
            return False
        return len(self.values[component]) > 1


@dataclass(slots=True)
class ViewerRouteComponentValueTracker:
    """Track observed component values for one routed viewer layer."""

    domains: dict[tuple[str, tuple[str, ...]], ViewerComponentValueDomain] = field(
        default_factory=dict
    )

    def update(
        self,
        route_key: str,
        axis_components: Sequence[str],
        layer_items: Sequence[ViewerComponentAddressedItem],
    ) -> None:
        self.domain_for(route_key, axis_components).replace_observed(layer_items)

    def update_component_values(
        self,
        route_key: str,
        axis_components: Sequence[str],
        component_values: ComponentValues,
    ) -> None:
        self.domain_for(route_key, axis_components).observe_component_values(
            component_values
        )

    def declare_component_values(
        self,
        route_key: str,
        axis_components: Sequence[str],
        component_values: ComponentValues,
    ) -> None:
        """Record the exact declared axis domain for one route generation."""

        self.domain_for(route_key, axis_components).declare(component_values)

    def domain_for(
        self,
        route_key: str,
        axis_components: Sequence[str],
    ) -> ViewerComponentValueDomain:
        domain_key = self.domain_key(route_key, axis_components)
        if domain_key not in self.domains:
            self.domains[domain_key] = ViewerComponentValueDomain.for_axes(
                axis_components
            )
        return self.domains[domain_key]

    def values_for(
        self,
        domain_key: tuple[str, tuple[str, ...]],
        axis_components: Sequence[str],
    ) -> ComponentValues:
        if domain_key not in self.domains:
            return {component: [] for component in axis_components}
        return self.domains[domain_key].observed()

    def purge(self, route_key: str) -> None:
        """Remove every component domain owned by one retired route."""

        for domain_key in tuple(self.domains):
            if domain_key[0] == route_key:
                self.domains.pop(domain_key)

    @staticmethod
    def domain_key(
        route_key: str,
        axis_components: Sequence[str],
    ) -> tuple[str, tuple[str, ...]]:
        return (route_key, tuple(axis_components))

    def shared_values_for(
        self,
        axis_components: Sequence[str],
    ) -> ComponentValues:
        """Derive the viewer-wide coordinate domain from routed domains.

        Route domains remain independently owned so route-local selection keeps
        its exact indices.  The shared domain is only a derived coordinate view:
        equal semantic values must occupy equal viewer coordinates even when the
        values arrived through different stream requests.
        """

        return {
            component: sorted(
                {
                    value
                    for domain in self.domains.values()
                    for value in domain.coordinate_values(component)
                },
                key=ViewerComponentValueOrdering.key,
            )
            for component in axis_components
        }


@dataclass(frozen=True, slots=True)
class ViewerLayerAxisProjection:
    """Route-local component axes projected into a shared viewer coordinate domain."""

    projected_axis_components: tuple[str, ...]
    component_values: ComponentValues
    routed_component_values: ComponentValues
    axis_offsets: tuple[int, ...]
    scalar_component_values: ComponentValues = field(default_factory=dict)
    routed_component_coordinates: tuple[ComponentCoordinate, ...] = field(
        default_factory=tuple
    )

    def axis_shape(self) -> tuple[int, ...]:
        """Return the viewer-domain stack shape for projected component axes."""
        return tuple(
            len(self.component_values[component])
            for component in self.projected_axis_components
        )

    def coordinate_index(
        self,
        components: Mapping[str, ComponentValue],
        *,
        context: str,
    ) -> tuple[int, ...]:
        """Return the projected viewer coordinate for one component address."""
        self.require_matching_scalar_components(components, context=context)
        return tuple(
            ViewerComponentCoordinateAuthority.index(
                components=components,
                component_values=self.component_values,
                component=component,
                context=context,
            )
            for component in self.projected_axis_components
        )

    def invalid_missing_indices(
        self,
        items: Sequence[ViewerComponentAddressedItem],
    ) -> tuple[tuple[int, ...], ...]:
        """Return route-local projected coordinates without payloads."""
        expected_indices = self.expected_indices()
        occupied_indices = {
            self.coordinate_index(item.address.components, context="viewer item")
            for item in items
        }
        return tuple(sorted(expected_indices - occupied_indices))

    def expected_indices(self) -> set[tuple[int, ...]]:
        """Return viewer coordinates backed by routed payload identities."""
        if not self.projected_axis_components:
            return {()}
        return {
            tuple(
                ViewerComponentCoordinateAuthority.value_index(
                    value=value,
                    component_values=self.component_values,
                    component=component,
                    context="viewer routed coordinate",
                )
                for component, value in zip(
                    self.projected_axis_components,
                    coordinate,
                    strict=True,
                )
            )
            for coordinate in self.routed_component_coordinates
        }

    def require_matching_scalar_components(
        self,
        components: Mapping[str, ComponentValue],
        *,
        context: str,
    ) -> None:
        """Validate component values collapsed out of the viewer axis projection."""
        for component, values in self.scalar_component_values.items():
            if len(values) != 1:
                raise ValueError(
                    f"Collapsed component {component!r} must have one value, "
                    f"got {values!r}."
                )
            value = ViewerComponentCoordinateAuthority.required_value(
                components,
                component,
                context=context,
            )
            if value != values[0]:
                raise ValueError(
                    f"{context} for collapsed component {component!r} has "
                    f"value {value!r}; expected {values[0]!r}."
                )

    def axis_offset(self, axis_index: int) -> int:
        """Return the viewer-domain offset for a projected axis."""
        if axis_index >= len(self.axis_offsets):
            return 0
        return self.axis_offsets[axis_index]

    def translate(self, payload_axis_labels: tuple[str, ...] = ()) -> tuple[float, ...]:
        return tuple(
            [
                *(float(offset) for offset in self.axis_offsets),
                *(0.0 for _ in payload_axis_labels),
                0.0,
                0.0,
            ]
        )


@dataclass(frozen=True, slots=True)
class ViewerLayerAxisProjectedComponent:
    """One component axis after route-local projection into viewer coordinates."""

    component: str
    values: list[ComponentValue]
    routed_values: list[ComponentValue]
    axis_offset: int


@dataclass(frozen=True, slots=True)
class ViewerLayerAxisProjectionStep:
    """Projection decision for one component axis."""

    component: str
    request: "ViewerLayerAxisProjectionRequest"

    def projected_axis(self) -> ViewerLayerAxisProjectedComponent | None:
        route_values = self.route_domain_values()
        if self.collapses_to_coordinate_singleton(route_values):
            return None
        values, offset = self.project_component_values()
        return ViewerLayerAxisProjectedComponent(
            component=self.component,
            values=values,
            routed_values=list(route_values),
            axis_offset=offset,
        )

    def collapsed_component_values(self) -> list[ComponentValue] | None:
        route_values = self.route_domain_values()
        if not self.collapses_to_coordinate_singleton(route_values):
            return None
        return list(route_values)

    def collapses_to_coordinate_singleton(
        self,
        coordinate_values: Sequence[ComponentValue],
    ) -> bool:
        return len(coordinate_values) == 1 and not (
            self.request.declared_domain.has_multiple_values(self.component)
            or self.request.viewer_domain.has_multiple_values(self.component)
        )

    def route_domain_values(self) -> list[ComponentValue]:
        if not self.request.route_domain.values.get(self.component, []):
            raise ValueError(
                f"route component domain for '{self.component}' is empty; "
                f"route_domain={self.request.route_domain.values!r}; "
                f"declared_domain={self.request.declared_domain.values!r}; "
                f"viewer_domain={self.request.viewer_domain.values!r}."
            )
        route_values = self.request.route_domain.required_values(self.component)
        self.request.declared_domain.require_contains(
            self.component,
            route_values,
            owner="declared",
        )
        self.request.viewer_domain.require_contains(
            self.component,
            route_values,
            owner="viewer",
        )
        return route_values

    def project_component_values(self) -> tuple[list[ComponentValue], int]:
        route_values = self.route_domain_values()
        coordinate_values = self.request.viewer_domain.required_values(self.component)
        route_indices = tuple(
            self.viewer_index(value, coordinate_values) for value in route_values
        )
        start_index = min(route_indices)
        stop_index = max(route_indices) + 1
        return list(coordinate_values[start_index:stop_index]), start_index

    def viewer_index(
        self,
        value: ComponentValue,
        viewer_values: Sequence[ComponentValue],
    ) -> int:
        try:
            return list(viewer_values).index(value)
        except ValueError as error:
            raise ValueError(
                f"Route component value {value!r} for '{self.component}' is absent "
                f"from viewer domain {list(viewer_values)!r}."
            ) from error


@dataclass(frozen=True, slots=True)
class ViewerLayerAxisProjectionRequest:
    """Typed domain bundle for projecting layer-local axes into viewer axes."""

    requested_components: tuple[str, ...]
    route_component_coordinates: tuple[ComponentCoordinate, ...]
    route_domain: ViewerComponentValueDomainView
    viewer_domain: ViewerComponentValueDomainView
    declared_domain: ViewerComponentValueDomainView

    @classmethod
    def from_component_values(
        cls,
        *,
        projected_axis_components: Sequence[str],
        route_component_coordinates: Sequence[Sequence[ComponentValue]] = (),
        route_component_values: ComponentValues,
        viewer_component_values: ComponentValues,
        declared_component_values: ComponentValues,
    ) -> "ViewerLayerAxisProjectionRequest":
        return cls(
            requested_components=tuple(projected_axis_components),
            route_component_coordinates=tuple(
                tuple(coordinate) for coordinate in route_component_coordinates
            ),
            route_domain=ViewerComponentValueDomainView(
                route_component_values,
                "route",
            ),
            viewer_domain=ViewerComponentValueDomainView(
                viewer_component_values,
                "viewer",
            ),
            declared_domain=ViewerComponentValueDomainView(
                declared_component_values,
                "declared",
            ),
        )

    def projection_steps(self) -> tuple[ViewerLayerAxisProjectionStep, ...]:
        return tuple(
            ViewerLayerAxisProjectionStep(
                component=component,
                request=self,
            )
            for component in self.requested_components
        )


class ViewerLayerAxisProjectionRequestAuthority:
    """Build viewer-axis projection requests from component-axis semantics."""

    @staticmethod
    def from_component_axis_semantics(
        *,
        route_key: str,
        component_axis_semantics: ViewerComponentAxisSemantics,
        layer_items: Sequence[ViewerComponentAddressedItem],
        route_value_tracker: ViewerRouteComponentValueTracker,
        aggregate_component_values: ComponentValues,
    ) -> ViewerLayerAxisProjectionRequest:
        axis_components = component_axis_semantics.layout.components_for_mode(
            ViewerComponentMode.STACK
        )
        route_value_tracker.update(route_key, axis_components, layer_items)
        if aggregate_component_values:
            route_value_tracker.update_component_values(
                route_key,
                axis_components,
                aggregate_component_values,
            )
        declared_component_values = component_axis_semantics.required_component_values(
            axis_components
        )
        route_value_tracker.declare_component_values(
            route_key,
            axis_components,
            declared_component_values,
        )
        viewer_component_values = route_value_tracker.shared_values_for(axis_components)
        return ViewerLayerAxisProjectionRequest.from_component_values(
            projected_axis_components=axis_components,
            route_component_coordinates=(
                ViewerLayerAxisProjectionRequestAuthority.route_coordinates(
                    axis_components=axis_components,
                    layer_items=layer_items,
                    aggregate_component_values=aggregate_component_values,
                )
            ),
            route_component_values=route_value_tracker.values_for(
                route_value_tracker.domain_key(route_key, axis_components),
                axis_components,
            ),
            viewer_component_values=viewer_component_values,
            declared_component_values=(
                component_axis_semantics.required_component_values(axis_components)
            ),
        )

    @staticmethod
    def route_coordinates(
        *,
        axis_components: Sequence[str],
        layer_items: Sequence[ViewerComponentAddressedItem],
        aggregate_component_values: ComponentValues,
    ) -> tuple[ComponentCoordinate, ...]:
        """Return exact routed coordinates, preserving cross-axis identity."""

        aggregate_components = tuple(
            component
            for component in axis_components
            if component in aggregate_component_values
        )
        aggregate_coordinates = tuple(
            product(
                *(
                    aggregate_component_values[component]
                    for component in aggregate_components
                )
            )
        )
        if not aggregate_coordinates:
            aggregate_coordinates = ((),)

        coordinates: set[ComponentCoordinate] = set()
        for item in layer_items:
            for aggregate_coordinate in aggregate_coordinates:
                components = {
                    **item.address.components,
                    **dict(
                        zip(
                            aggregate_components,
                            aggregate_coordinate,
                            strict=True,
                        )
                    ),
                }
                coordinates.add(
                    ViewerComponentCoordinateAuthority.value_tuple(
                        components,
                        axis_components,
                        context="viewer routed item",
                    )
                )
        return tuple(sorted(coordinates, key=ViewerComponentValueOrdering.tuple_key))


class ViewerLayerAxisProjector:
    """Project route component values into the current viewer axis domain."""

    def project(
        self,
        request: ViewerLayerAxisProjectionRequest,
    ) -> ViewerLayerAxisProjection:
        steps = request.projection_steps()
        projected_axes = tuple(
            projected_axis
            for step in steps
            if (projected_axis := step.projected_axis()) is not None
        )
        scalar_component_values = {
            step.component: values
            for step in steps
            if (values := step.collapsed_component_values()) is not None
        }

        return ViewerLayerAxisProjection(
            projected_axis_components=tuple(axis.component for axis in projected_axes),
            component_values={axis.component: axis.values for axis in projected_axes},
            routed_component_values={
                axis.component: axis.routed_values for axis in projected_axes
            },
            routed_component_coordinates=tuple(
                dict.fromkeys(
                    tuple(
                        coordinate[request.requested_components.index(axis.component)]
                        for axis in projected_axes
                    )
                    for coordinate in request.route_component_coordinates
                )
            ),
            axis_offsets=tuple(axis.axis_offset for axis in projected_axes),
            scalar_component_values=scalar_component_values,
        )


class ViewerComponentCoordinateAuthority:
    """Fail-loud component coordinate lookup shared by viewer backends."""

    @staticmethod
    def required_value(
        components: Mapping[str, ComponentValue],
        component: str,
        *,
        context: str,
    ) -> ComponentValue:
        if component not in components:
            raise ValueError(f"{context} missing stack component {component!r}.")
        return components[component]

    @staticmethod
    def required_axis_values(
        component_values: ComponentAxisValues,
        component: str,
        *,
        context: str,
    ) -> Sequence[ComponentValue]:
        if component not in component_values:
            raise ValueError(f"{context} missing axis domain for {component!r}.")
        values = component_values[component]
        if not values:
            raise ValueError(f"{context} axis domain for {component!r} is empty.")
        return values

    @classmethod
    def index(
        cls,
        *,
        components: Mapping[str, ComponentValue],
        component_values: ComponentAxisValues,
        component: str,
        context: str,
    ) -> int:
        value = cls.required_value(
            components,
            component,
            context=context,
        )
        return cls.value_index(
            value=value,
            component_values=component_values,
            component=component,
            context=context,
        )

    @classmethod
    def value_index(
        cls,
        *,
        value: ComponentValue,
        component_values: ComponentAxisValues,
        component: str,
        context: str,
    ) -> int:
        """Return the positional index for one semantic component value."""
        values = cls.required_axis_values(
            component_values,
            component,
            context=context,
        )
        try:
            return list(values).index(value)
        except ValueError as error:
            raise ValueError(
                f"{context} component {component!r} value {value!r} is outside "
                f"axis domain {list(values)!r}."
            ) from error

    @classmethod
    def value_tuple(
        cls,
        components: Mapping[str, ComponentValue],
        axis_components: Sequence[str],
        *,
        context: str,
    ) -> tuple[ComponentValue, ...]:
        return tuple(
            cls.required_value(
                components,
                component,
                context=context,
            )
            for component in axis_components
        )


class ViewerDimensionValueAuthority:
    """Collect and index tuple-valued dimensions for viewer coordinate systems."""

    @classmethod
    def collect_from_payloads(
        cls,
        items: Sequence[Mapping[str, ComponentValue | Mapping[str, ComponentValue]]],
        components: Sequence[str],
    ) -> list[tuple]:
        if not components:
            return [()]

        values = {cls.value_tuple(cls.metadata(item), components) for item in items}
        return sorted(values, key=ViewerComponentValueOrdering.tuple_key)

    @staticmethod
    def merge(
        stored_values: Sequence[tuple], new_values: Sequence[tuple]
    ) -> list[tuple]:
        return sorted(
            set(stored_values) | set(new_values),
            key=ViewerComponentValueOrdering.tuple_key,
        )

    @staticmethod
    def metadata(
        item: Mapping[str, ComponentValue | Mapping[str, ComponentValue]],
    ) -> Mapping[str, ComponentValue]:
        metadata = item["metadata"]
        if not isinstance(metadata, Mapping):
            raise TypeError("Viewer payload metadata must be a mapping.")
        return metadata

    @staticmethod
    def value_tuple(
        metadata: Mapping[str, ComponentValue],
        components: Sequence[str],
    ) -> tuple:
        return ViewerComponentCoordinateAuthority.value_tuple(
            metadata,
            components,
            context="Viewer dimension metadata",
        )

    @classmethod
    def index(
        cls,
        metadata: Mapping[str, ComponentValue],
        components: Sequence[str],
        dimension_values: Sequence[tuple],
    ) -> int:
        key = cls.value_tuple(metadata, components)
        try:
            return list(dimension_values).index(key)
        except ValueError as error:
            raise ValueError(
                "Viewer dimension metadata tuple "
                f"{key!r} is outside axis domain {list(dimension_values)!r}."
            ) from error
