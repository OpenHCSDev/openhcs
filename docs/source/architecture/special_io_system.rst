Special I/O terminology (transition)
====================================

.. important::

   This URL is retained for compatibility. The old string-keyed special-I/O and
   generated-pickle-path architecture has been superseded by typed callable
   contracts and compiled artifact plans. Read :doc:`artifact_contract_system`.

``special_inputs`` is callable-ABI metadata. It names Python input parameters; they do not own artifact type, producer identity, materialization, or
runtime storage.

Current ownership is split across:

- ``CallableContract`` input/output declarations for the generic callable ABI;
- ``CellProfilerModuleArtifactContracts`` for deriving one CellProfiler
  invocation's callable declarations from setting bindings and module hooks;
- ``ArtifactGraph`` and typed artifact plans during compilation;
- ``RuntimeValueStore`` and nominal runtime values during execution;
- PolyStore for generic persistence formats and backend mechanics.

See also :doc:`source_model`, :doc:`pipeline_compilation_system`, and
:doc:`runtime_value_system`.
