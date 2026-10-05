from dataclasses import replace

from openhcs.core.artifacts import ArtifactSpec, ImageArtifactType
from openhcs.core.callable_contract import CallableContract, CallableMetadata
from openhcs.core.runtime_adapters import RuntimeAdapterSpec


def test_custom_runtime_wrapper_is_retained_for_its_exact_contract():
    prepared = []

    def raw(image):
        return image

    def runtime_callable(registered_func, contract):
        prepared.append(contract)

        def execute(image):
            return contract.artifact_outputs[0].name, registered_func(image)

        return execute

    first = CallableContract(
        func=raw,
        function_name=raw.__name__,
        module_name=raw.__module__,
        metadata=CallableMetadata(
            input_memory_type="python",
            output_memory_type="python",
            artifact_outputs=(ArtifactSpec.output("First", ImageArtifactType),),
            runtime_adapter=RuntimeAdapterSpec(
                parameter_name="runtime",
                factory=lambda request: request,
                runtime_callable_factory=runtime_callable,
            ),
        ),
    )
    second = replace(
        first,
        metadata=replace(
            first.metadata,
            artifact_outputs=(ArtifactSpec.output("Second", ImageArtifactType),),
        ),
    )
    first_callable = first.resolve_runtime_callable()
    second_callable = second.resolve_runtime_callable()
    assert first_callable(7) == ("First", 7)
    assert second_callable(9) == ("Second", 9)
    assert first.resolve_runtime_callable() is first_callable
    assert second.resolve_runtime_callable() is second_callable
    assert len(prepared) == 2
    assert prepared[0] is first and prepared[1] is second
