# Shared abstractions

**Read this before any surface file.** Each mechanism is defined once, here. A surface file says what it builds and uses and links back; it never re-specifies an abstraction. If a surface needs an extension, the builder makes it; nobody forks it.

Most mechanisms this refactor needs already exist (see the exemplars in [00-RULES.md](00-RULES.md#project-specifics)). Only two new ones are needed by three or more surfaces.

| ID | Abstraction | Built by | Wave | Used by |
|---|---|---|---|---|
| [A1](#a1-imagepayload-family-methods) | `ImagePayload` family methods | K1 | 3 | K1, K2, K5 |
| [A2](#a2-dataclass-derived-record-codec) | Dataclass-derived record codec | C6 | 2 | C6, K6, K5 |

## A1 ImagePayload family methods

**What it is.** A user function returns either a bare array or a metadata carrier. Today that answer is re-decided by `image_payload_data/metadata/mask/geometry` switches (`core/runtime_image_values.py:1508-1533`) at 513 call sites. A1 wraps the return once at the function boundary into one `ImagePayload` family, whose members own the behaviour now written as switches:

```python
class ImagePayload(ABC):
    data: ArrayLike
    metadata: ImagePayloadMetadata
    def mask(self) -> ArrayLike | None: ...
    def alignment_slices(self, axis: AlignmentAxis) -> tuple[ImagePayload, ...]: ...
    def map_slices(self, fn: Callable[[ImagePayload], ImagePayload]) -> ImagePayload: ...
```

`RuntimeSliceProjectableValue` (`core/runtime_plane_projection.py:19`) is the existing exemplar: payload members join it instead of `RuntimeSliceProjectionStrategy`'s type-keyed table.

**Replaces:** the four accessor switches and their 513 consumers; `payload_slices_for_alignment` (`aligned_image_payload.py:1950`); 18 direct carrier checks; the three switches in `steps/function_runtime.py` (1069, 1196, 1235); 31 hand-written `for i in range(x.slice_count)` loops (11 in `artifacts.py`).
**Used by:** K1 (builds it, migrates runtime values and function runtime), K2 (artifact kinds call `map_slices` and payload methods instead of `isinstance`), K5 (invocation side of the callable contract receives payloads, never bare arrays).
**Built by:** K1, wave 3, as a new module first.

## A2 Dataclass-derived record codec

**What it is.** One codec that encodes and decodes a frozen dataclass from its field declarations, so no record's field list is written by hand. It extends the existing `serialization/json.to_jsonable` and `DebugJsonCodec.dataclass_from_record` (`core/debug.py:416`); it does not add a third mechanism. Enums travel as members inside the process and as their declared names only at the wire.

**Replaces:** `ProgressEvent.from_dict`/`to_dict` and the `emit()` kwargs (six restatements of one field list, `core/progress/types.py:514-710`); the four hand-written `DebugSnapshot` record shapes (`core/debug.py:903, 928, 1787`); `CallableMetadata.as_namespace` (21 hand writes, `core/callable_contract.py:753`).
**Used by:** C6 (progress events), K6 (debug snapshots), K5 (callable metadata).
**Built by:** C6, wave 2.

## Build order at a glance

```
wave 2: C6 builds A2
wave 3: K1 builds A1; K6 and K5 use A2; K2 and K5 use A1 after K1 lands
```
