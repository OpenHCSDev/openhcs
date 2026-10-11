Compiler extensions
===================

Compiler phases operate on a ``CompilationSession`` and mutate typed
``CompiledStepPlan`` fields. They do not reinterpret ObjectState or maintain a
parallel dictionary plan.

Invariants
----------

``ResolvedPipelineDefinition`` captures the enabled steps with their
ObjectState scope identities and provenance, and admits their artifact
contracts and forward topology once before axis fan-out. ``CompilationSession``
binds that definition to one ``ProcessingContext`` (one axis or sequential
combination), its compiled-plan map, source projection, and dataset scope;
``plan(index)`` fails when a step has no compiled plan.

Adding a decision
-----------------

1. Identify the declaration or previous typed plan field that supplies the
   input fact.
2. Add a compiler phase only if no existing phase owns the decision.
3. Store a result needed downstream in a typed plan field or typed plan object.
4. Validate the invariant when the result is constructed.
5. Make execution consume the compiled result without fallback discovery.

For framework resources, extend the callable or ArrayBridge declaration that
owns the memory role, then compile the derived binding onto
``CompiledStepPlan``. Do not restore a process-global GPU scheduler or validator
beside the typed plan.

Artifact planning uses exact ``ArtifactSpecRef`` identity. Source- or
metadata-satisfied inputs need not have runtime plans. A selector must only
exact-match a plan that is present.

Tests should cover the session invariant, the phase's typed output, one missing
or ambiguous declaration failure, and a minimal compile-to-bundle path.

See :doc:`../architecture/pipeline_compilation_system`.
