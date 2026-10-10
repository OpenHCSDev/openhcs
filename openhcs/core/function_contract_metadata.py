"""Dependency-free callable contract metadata keys."""

from __future__ import annotations

from typing import ClassVar


class FunctionContractAttribute:
    """Callable namespace keys owned by function-level contract decorators."""

    artifact_inputs: ClassVar[str] = "__artifact_inputs__"
    artifact_outputs: ClassVar[str] = "__artifact_outputs__"
    processing_contract: ClassVar[str] = "__processing_contract__"
    execution_scope: ClassVar[str] = "__openhcs_execution_scope__"
    declared_processing_contract: ClassVar[str] = (
        "__openhcs_declared_processing_contract__"
    )
    raw_processing_function: ClassVar[str] = "__openhcs_raw_processing_function__"
    canonical_signature: ClassVar[str] = "__openhcs_canonical_signature__"
    raw_runtime_signature: ClassVar[str] = "__openhcs_raw_runtime_signature__"
    processing_prepare: ClassVar[str] = "__openhcs_prepare__"
    runtime_adapter: ClassVar[str] = "__runtime_adapter__"
    runtime_image_execution_mode: ClassVar[str] = (
        "__openhcs_runtime_image_execution_mode__"
    )
    callable_request_binding: ClassVar[str] = "__openhcs_callable_request_binding__"
    special_inputs: ClassVar[str] = "__special_inputs__"
    artifact_input_parameter_names: ClassVar[str] = (
        "__openhcs_artifact_input_parameter_names__"
    )
    runtime_bound_parameters: ClassVar[str] = "__openhcs_runtime_bound_parameters__"
    runtime_context_parameter: ClassVar[str] = "__openhcs_runtime_context_parameter__"
    required_axis_roles: ClassVar[str] = "__openhcs_required_axis_roles__"
    variable_component_stack_requirement: ClassVar[str] = (
        "__openhcs_variable_component_stack_requirement__"
    )
    allowed_group_by_roles: ClassVar[str] = "__openhcs_allowed_group_by_roles__"
    object_label_input_execution_mode: ClassVar[str] = (
        "__object_label_input_execution_mode__"
    )
    image_payload_consumption: ClassVar[str] = "__openhcs_image_payload_consumption__"
    primary_image_carrier_requirement: ClassVar[str] = (
        "__openhcs_primary_image_carrier_requirement__"
    )
    primary_image_carrier_transition: ClassVar[str] = (
        "__openhcs_primary_image_carrier_transition__"
    )
    declaration_revision: ClassVar[str] = "__openhcs_declaration_revision__"

    declaration_validation: ClassVar[str] = "__openhcs_declaration_validation__"
