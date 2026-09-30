# Compiler preparation ownership decision

OpenHCS source: `f75f766743460d2cf2902d8c0535126d95405e60`.
Advisor source: `0844525` in an isolated clean worktree; the user's dirty
`/home/ts/code/NominalRefactorAdvisor` checkout is preserved.
Guidance: packaged `skills/nra-refactoring/SKILL.md`. The exact requested
`refactor-audit` skill has not been located; its identity remains OPEN.

## Admitted intent and measured payoff

The user authorizes a nominal compiler refactor with shared inherited algorithms,
elimination of duplicated decisions, and subsequent caching to approach a few
seconds of compilation. Preserve processing outputs and eager preparation before
timed execution. This admits the following bounded ownership decision without
requiring another permission request; it does not prove behavioral equivalence.

The real compiler trace spends 23.712278 of 24.654537 seconds in preparation.
Planning accounts for less than one second and is rejected as the dominant route.
Child intensity and shape warmups take 11.15 and 10.61 seconds; subsequent parent
primary-object and shape hooks take 6.59 and 3.13 seconds. A serial kernel probe
also identifies 5.679 seconds of 2D quantile compilation, including 4.413 seconds
in its partition helper. These are nested inclusive times, not additive costs.

This migration is an explicitly requested structural dependency of changing
preparation scheduling and artifact reuse. It claims no immediate LLVM speedup.
Its production consumer is the existing compiled-context preparation boundary.
Unconditional forking of warm preparation was already rejected by replay:
0.338 seconds serial versus 0.704 seconds fork plus parent hydration.

## Determining declarations and executable consumers

- `callable_contract.py:147`: `CompilerPreparedAutoRegisterFamily` determines
  family preparation and child-cache eligibility. Its backend implementations
  remain the authority; the core does not inspect provider names or Numba flags.
- `autoregister_preparation.py:96`: registry ownership is derived from module
  declarations and deduplicated by actual registry identity. Public discovery
  retains unrelated registry discovery, while preparation filters nominally
  before touching lazy registries. Export this existing operation for consumers;
  do not reconstruct it elsewhere.
- `callable_contract.py:1570` and metadata declarations: callable/module hooks
  remain explicit callable metadata. A module may have no hook, and a callable
  may have no module. Metadata boundary validation remains required.
- `callable_contract.py:1669,1716`: two paths repeat completion checking,
  execution and successful completion marking. Their identity policies differ:
  module hooks use callable object identity; callable hooks use declaring
  callable name plus hook module/qualname, including equivalent bound methods.
- `function_runtime.py:247,1683,1689`: runtime callable resolution is bound to
  each compiled contract. Parent preparation follows child cache population and
  remains in invocation order. These actual consumers must use the shared
  preparation contract after migration.
- `_backend.py:418`: the registry-snapshot kernel cache has a different lifetime
  and invalidation contract from core hook completion. It remains independently
  owned by the backend; it is not an obsolete duplicate readiness authority.

## Required and forbidden pairs (R*)

| Implementation fact | Consumer | Required answer / admitted owner |
|---|---|---|
| Process-local preparation completion | Module registry, module hook, callable hook | Shared `PreparationOperation.prepare` algorithm; mark only after success |
| Hook execution | Module and callable hook operations | Inherited declared-hook execution; leaves supply identity policy only |
| Module registry membership | Parent module preparation and child projection | Existing `AutoRegisterRegistryPreparation.module_registry_owners` derived discovery |
| Persistent cache child eligibility | Generic child scheduler | Family's public `can_prepare_in_child`, default opt-out |
| Parent readiness | Compiled invocation consumer | Parent operations execute after cache children; child success never marks parent ready |
| Runtime adapter callable identity | Invocation resolver | Existing exact compiled-contract cache; preparation keys must not replace it |
| Backend specialization readiness | Backend consumers | Existing registry snapshot cache; core completion must not invalidate it |

Forbidden: a second hook completion set; a second registry scan or class roster;
backend/provider case switches in the compiler scheduler; accepting a child result
as parent readiness; swallowed child or hook failures; new optional-import catches;
pre-validating later hooks before preceding family/module effects; moving a cache
hit into the execution timer to manufacture faster compilation.

Preparation keys are internal value-only hashable identities. No consumer decodes
their tuple fields or dispatches on them; no enum or extra identity-class roster is
needed. Concrete operation classes retain the distinct behavior and lifecycle.
The operation ABC owns the shared completion algorithm. The existing module and
callable declarations determine operation membership; the batch owns scheduling.

## Migration and new-case experiment

Introduce a preparation operation ABC with shared completion and failure semantics;
derive module-registry, registry-family and declared-hook operations; share hook
execution through inheritance, retaining module/callable identity policies.
Create callable operations lazily so registry -> module hook -> callable hook
effect and validation order stays intact. Move the sole child scheduler to a
generic cache batch over operation projections. Migrate the real compiler boundary
and existing public helper entry points. Delete the old private completion set,
duplicated module/callable implementations and family-specific scheduler.

A newly declared compiler-prepared registry family must participate without
editing scheduler membership. A new hook type must inherit the common execution
algorithm and need only supply its distinguishing identity. Test actual compiler
consumer order, equivalent bound-method identities, hook replacement, failed-hook
retry, invalid-hook validation after prior effects, fork child PIDs and registry
deduplication. Preserve unsupported-fork short-circuit and warm-cache opt-out.

## Coverage and proof limits

The NRA syntax census covers all 696 original production modules and 5,014 original
classes; 5,002 join the compact class projection. The 12 conditional/function-local
unprojected declarations remain OPEN in the saved census, outside this migration.
The full semantic scan with all-package context exceeded the explicit 165-second
shell budget (exit 124); retain its empty output and stderr as timeout evidence.
A completed two-module focused raw scan reported zero findings in 0.783 seconds;
that is not a global ownership or equivalence proof. A four-module raw scan is
pending. No raw mapping/record finding is promoted from an incomplete scan.

The migration requires authored nominal operations and lazy metadata effects;
NRA has no synthesized equivalence recipe for this behavior. Use its supported
exact target patches and new-file operation for a source-checked transaction,
label the body changes authored, inspect one combined diff, and validate behavior
through the existing and new consumer tests plus ordinary cold/warm benchmark
output parity. Do not describe syntax preflight or an empty guard suite as proof.

OPEN: exhaustive dynamic monkeypatch/alias behavior, independent native execution
equivalence proof, whole-package detector completion, exact refactor-audit skill
identity, general cold kernel compilation below a few seconds, and issue #162's
remaining lazy-JIT execution boundaries. None is claimed complete by this refactor.
