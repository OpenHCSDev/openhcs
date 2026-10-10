# L1: Strategy mixins and the cache family move to metaclass-registry

**Head audited:** `openhcs` `main` at `9a2550401` (#1163); `metaclass-registry` `main` at `393a7e0` (v0.2.2). **Rules:** [00-RULES.md](00-RULES.md). **Step 2.**
**Shared abstractions:** none built or used from [02-SHARED-ABSTRACTIONS.md](02-SHARED-ABSTRACTIONS.md). The two mechanisms are the `registry_strategies` and `BoundedCache` exemplars named in 00-RULES; this surface moves them to the library that owns registries.

## What is wrong

**Two generic AutoRegisterMeta mechanisms live in OpenHCS, and the cache family's membership is declared twice, with a gap.**

- `openhcs/core/registry_strategies.py` (506 lines) holds `EnumKeyedStrategyMixin`, `NominalTypeKeyedStrategyMixin`, `NominalTypeStrategyFamilyMixin`, `MostDerivedContextStrategyMixin`, `StrategyLabelRegistryMixin`, `AlwaysMatchesContextMixin`, `RegisteredLeafClassSpec`/`GeneratedLeafClassSpec` and the enum-payload helpers. Nothing in it is OpenHCS-specific: it imports only `metaclass_registry`. 60 production modules and `benchmark/equivalence/runtime.py` import it.
- It re-exports `RegisteredEnumMeta` from `metaclass_registry` (one importer).
- `GeneratedEnumClassSpec` has no user anywhere.
- `__enum_label_attr__` is declared on `EnumKeyedStrategyMixin` and restated on 17 strategy roots; nothing reads it (each root's `__registry_key__` already names the label). `stable_key_axis` is declared on six classes and written by `MostDerivedContextStrategyMeta`; nothing reads it. 29 dead declarations in total.
- `openhcs/core/process_local_cache.py` (183 lines) has two registered roots, `RegisteredProcessLocalBoundedCache` (keyed by `__name__`) and `IdentityBoundProcessCache` (keyed by a hand-written `registry_key`, skipped when absent). The clear-all loop is written on both (`:133-137`, `:152-156`) and a third function calls both (`:180-183`).
- Membership gap: an `IdentityBoundProcessCache` subclass that forgets `registry_key` is silently not registered, so clear-all never clears it. `CallableContractRuntimeCache.registry_key` exists only to avoid that.
- `ProcessLocalBoundedCache` (unregistered singleton) has no production subclass outside the registered root; it is a second mode of the same family.
- `identity_owner_tuples_match` and `named_identity_owner_tuples_match` have no caller.
- The clear-all function `clear_registered_process_local_caches` has no production caller; only tests clear caches.
- The strategy mixins memoize registry views (`registered_strategy_types`, `strategy_type_for_enum_member`, `strategy_types_for_nominal_type`) with `lru_cache` forever, so a member declared after the first lookup is never selected.

## Target

`metaclass_registry.strategies`: the strategy mixins, moved unchanged except for deleting `__enum_label_attr__`, `stable_key_axis` and `GeneratedEnumClassSpec`, and rebuilding the memoized registry views whenever a family gains a member. `AutoRegisterMeta` forwards class keywords to `__init_subclass__`, which the folded cache root needs for cooperative subclass hooks.

`metaclass_registry.caches`: one registered family.

```python
class BoundedCache(Generic[K, V]): ...                 # LRU values, lifetime owned by the consumer
class SynchronizedBoundedCache(BoundedCache[K, V]): ... # one instance lock
class ProcessLocalBoundedCache(BoundedCache[K, V], metaclass=AutoRegisterMeta):
    # every subclass is a member by inheritance (key: module.ClassName); one singleton per class
    @classmethod
    def clear_process_caches(cls) -> None: ...         # clears every member that is a subclass of cls
class IdentityBoundProcessCache(ProcessLocalBoundedCache[int, tuple[object, Any]]): ...  # get_bound / put_bound
```

Deleted: `RegisteredProcessLocalBoundedCache` (folded into `ProcessLocalBoundedCache`), the second registry and its `registry_key`, both per-root clear-all copies and `clear_registered_process_local_caches`, the two dead owner-tuple helpers, `CallableContractRuntimeCache.registry_key`, both OpenHCS modules, and `tests/unit/test_process_local_cache.py` (its behavioural cases move into the library's family tests; the OpenHCS-domain membership check stays as one test). Every importer imports from `metaclass_registry.strategies` / `metaclass_registry.caches` directly. No re-export.

Lockstep: library 0.3.0 (new public modules), OpenHCS pin `metaclass-registry>=0.3.0,<0.4`, submodule pointer at the library branch commit. The OpenHCS PR merges after the library PR is merged and tagged.

## Guards

`tests/unit/test_registry_library_boundary.py`:
- AST: no Python file under `openhcs/`, `benchmark/`, `tests/` or `scripts/` imports `openhcs.core.registry_strategies` or `openhcs.core.process_local_cache`, and neither module file exists.
- AST: no class under `openhcs/` assigns `__enum_label_attr__` or `stable_key_axis`, and no direct `ProcessLocalBoundedCache`/`IdentityBoundProcessCache` subclass assigns `registry_key`.

## Tests

- Library: one family-level test per mechanism (enum-keyed, nominal-type, most-derived context, generated leaf, enum payload helpers; bounded LRU, synchronized, process-local singleton per class, membership by inheritance and clear-all, identity binding).
- OpenHCS: one test that every OpenHCS process-local cache domain is a registered member and cleared by the family's clear-all; the store-query caches stay plain `BoundedCache`. The strategy families are already exercised by `test_cellprofiler_strategy_registries.py` and the other family users.

## New-case experiments

Today, a new identity-bound cache needs a subclass plus a unique `registry_key`, or clear-all silently skips it; a new strategy root restates `__enum_label_attr__`. After: one subclass declaration in each case.

## Done when

Both OpenHCS modules are deleted, every importer reads the library, the guards pass, the library tests and the OpenHCS registry/cache tests pass against the library branch, and the library PR is open with the version bump.
