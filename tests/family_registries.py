"""Family registries as tests see them.

A family registry is process-wide: a class is a member from the moment it is
created until the process ends. Tests declare members of production families
(stand-ins) all the time, at module level and inside test functions. This
module is the one place that keeps those declarations from outliving the
tests they belong to:

* a member a test module declares at import is a member only while that
  module's tests run (and the tests of modules that import it);
* whatever a test does to a registry, declaring a member, removing one or
  replacing one, is undone when the test ends.

``tests/conftest.py`` wires these into collection and into every test, so no
test needs cleanup code of its own.
"""

import sys
from abc import ABCMeta
from collections import defaultdict
from collections.abc import Hashable, Iterator
from types import ModuleType

from metaclass_registry import AutoRegisterMeta
from metaclass_registry.strategies import _invalidate_family_projections

Registry = dict[Hashable, object]
Entry = tuple[Registry, Hashable, object]
Snapshot = list[tuple[Registry, dict[Hashable, object]]]

TESTS_PACKAGE = __name__.partition(".")[0]

_registries: dict[int, Registry] = {}
_modules_walked = 0
_module_members: defaultdict[str, list[Entry]] = defaultdict(list)


def declared_by_tests(member: object) -> bool:
    """Whether ``member`` is a class a test declared.

    That is a class defined in the tests package, or one a test made by calling
    the registering metaclass (``type(name, bases, namespace)``): such a class
    has no declaring module and ``ABCMeta`` names it after its own, ``abc``.
    No production member is made that way.
    """
    return isinstance(member, type) and (
        member.__module__.partition(".")[0] == TESTS_PACKAGE
        or member.__module__ == ABCMeta.__module__
    )


def family_registries() -> tuple[Registry, ...]:
    """Every family registry in the process.

    Families are created by importing the module that declares their root, so
    the class graph is walked again only when a module has been imported.
    """
    global _modules_walked
    if len(sys.modules) != _modules_walked:
        seen: set[type] = set()
        pending: list[type] = [object]
        while pending:
            for subclass in type.__subclasses__(pending.pop()):
                if subclass in seen:
                    continue
                seen.add(subclass)
                pending.append(subclass)
                if isinstance(subclass, AutoRegisterMeta):
                    registry = getattr(subclass, "__registry__", None)
                    if isinstance(registry, dict):
                        _registries[id(registry)] = registry
        _modules_walked = len(sys.modules)
    return tuple(_registries.values())


def _test_entries() -> Iterator[Entry]:
    for registry in family_registries():
        for key, member in list(dict.items(registry)):
            if declared_by_tests(member):
                yield registry, key, member


def withdraw_module_members() -> None:
    """Take members declared by test modules out of their families.

    Called after each test module is imported. The members are remembered by
    declaring module for ``module_members``.
    """
    withdrawn = False
    for registry, key, member in _test_entries():
        dict.pop(registry, key)
        _module_members[member.__module__].append((registry, key, member))
        withdrawn = True
    if withdrawn:
        _invalidate_family_projections()


def _test_modules_used_by(module: ModuleType) -> set[str]:
    """``module`` and the test-package modules its globals come from, transitively."""
    used: set[str] = set()
    pending = [module.__name__]
    while pending:
        name = pending.pop()
        if name in used or name not in sys.modules:
            continue
        used.add(name)
        for value in list(vars(sys.modules[name]).values()):
            source = value.__name__ if isinstance(value, ModuleType) else getattr(value, "__module__", None)
            if isinstance(source, str) and source.partition(".")[0] == TESTS_PACKAGE:
                pending.append(source)
    return used


def join_module_members(module: ModuleType) -> None:
    """Make the members declared by ``module`` and the test modules it uses members again."""
    joined = False
    for name in _test_modules_used_by(module):
        for registry, key, member in _module_members.get(name, ()):
            holder = dict.get(registry, key, member)
            if holder is not member:
                raise RuntimeError(
                    f"{member.__module__}.{member.__qualname__} is declared under the "
                    f"registry key {key!r}, which {holder!r} holds."
                )
            dict.__setitem__(registry, key, member)
            joined = True
    if joined:
        _invalidate_family_projections()


def leave_module_members() -> None:
    """Take every member declared by tests out of its family."""
    left = False
    for registry, key, _member in _test_entries():
        dict.pop(registry, key)
        left = True
    if left:
        _invalidate_family_projections()


def registry_snapshot() -> Snapshot:
    return [(registry, dict(dict.items(registry))) for registry in family_registries()]


def restore_registries(before: Snapshot) -> None:
    """Undo what a test did to the registries in ``before``.

    Members production code discovered during the test stay: discovery is
    lazy and happens once. Members the test declared go; members it removed
    or replaced come back.
    """
    snapshots = {id(registry): members for registry, members in before}
    changed = False
    for registry in family_registries():
        members = snapshots.get(id(registry), {})
        for key, member in list(dict.items(registry)):
            if declared_by_tests(member) and members.get(key) is not member:
                dict.pop(registry, key)
                changed = True
        for key, member in members.items():
            if dict.get(registry, key) is not member:
                dict.__setitem__(registry, key, member)
                changed = True
    if changed:
        _invalidate_family_projections()
