Runtime values, stores, and projection
======================================

OpenHCS runtime data is not limited to ndarrays. Images, object labels,
measurements, relationships, spatial grids, sparse labels, and tables carry
different invariants and projection behavior. Each family has a nominal value
type rather than a shared dictionary payload.

Value families
--------------

``RuntimeArrayPayload``
  Nominal array protocol with explicit NumPy interoperation.

image payloads
  ``ImagePayload``: image data plus mask, declared payload axes, plane-axis
  declaration, source metadata, spatial domain, and source-plane provenance.

object-label values
  Dense or sparse labeled-object domains, grouped sets, and storage/building
  strategies.

``MeasurementTable`` and ``ColumnarRows``
  Typed measurement and tabular values with row/column semantics.

``ObjectRelationship``
  Directed parent/child or other object relationships with endpoint identity.

``SparseIJVLabelRows`` and ``SpatialGrid``
  Sparse label and grid domains used by segmentation and measurement modules.

Artifact identity
-----------------

``RuntimeValue`` pairs a payload with an ``ArtifactKey``. The key contains the
semantic artifact name/type, execution-axis scope, optional component group, and
semantic identity. Persistence location is represented separately by
``RuntimeArtifactLocation``.

Invocation-selected output plans remain keyed by ``ArtifactSpecRef`` when they
enter ``RuntimeAdapterRequest``. ``CallableContract.resolve_returned_plan_values``
binds returned positions to the exact plan/spec refs, and adapter lookup accepts the
declaration-derived ref whose key agrees with its plan. Two outputs may
therefore share a name when their artifact types differ: selection, matching,
and request lookup preserve both identities rather than collapsing to the name.

RuntimeValueStore
-----------------

Each processing context owns a ``RuntimeValueStore``. It is the source of truth
for:

- validating and recording typed values
- exact current binding by artifact key and backend location
- explicit replacement when a later producer supersedes a binding
- typed queries derived from compiled artifact edges
- append-only observations and revision-safe query caches

Runtime consumers resolve an exact ``RuntimeArtifactQuery``. Missing,
ambiguous, incorrectly typed, or incorrectly scoped results are errors; the
store does not guess from filenames or search a fallback chain.

Axis and group scope
--------------------

``RuntimeExecutionAxisScope`` identifies the compiled execution axis and optional
component group. ``ComponentGroupScope`` is used at declaration/plan time and
can represent ungrouped, fixed, or dynamic group selection. These scopes are
part of artifact identity rather than encoded into ad hoc path strings.

Runtime slice projection
------------------------

Each owned runtime value family subclasses ``RuntimeSliceProjectableValue`` and
implements its own slice behaviour: slice count, declared plane axis, per-slice
values, and alignment slices. Projection uses explicit plane-axis and
source-identity declarations.

Image payloads, aligned value sets, object labels, columnar rows (including
measurement tables and sparse labels), relationships, and identity-projectable
semantic values implement it. ``RuntimeSliceProjection`` handles only foreign
values: it lists the array, mapping and primitive types that carry no
runtime-slice axis, and projects tuples and lists item by item. Any other value
without the ABC is an error. If a new value family can carry a runtime slice, it
must subclass ``RuntimeSliceProjectableValue``.

Function-output contextualization
---------------------------------

A callable return does not inherit context from whichever runtime value happens
to be nearby. The exact compiled output artifact type first selects behaviour
through its ``ArtifactType.contextualize_output`` method. For an image output,
``ImageArtifactType`` then calls ``contextualize_image_output`` on the source
value chosen by the output's compiled ``source_context_source`` relation, so the
source's nominal type decides. This is a two-stage owner dispatch, not a table
of callable names or payload shapes.

An image result that already carries context may bypass derivation only when its
source identity is complete and, for a declared artifact output, its represented
source identities exactly align with the source surfaces. Otherwise the selected
source strategy attaches context and validates the plane projection. Aligned
value sets preserve per-slice context and require their count to match the
declared runtime-slice axis.

Image results that select or reorder source planes implement
``SourceProjectedImageOutput``. Their leaf implementation validates the declared
selection and projects source metadata before generic image contextualization.
``SelectedPlaneImageOutput`` carries a cropped array and its ordered source
indices, preserving source-plane identity even when only one plane remains.

Object-label sources have a specialized image-output rule. A rendered label
volume with no selected plane must acquire the invocation's declared plane axis,
including when the volume depth is one. Its source-plane provenance count and
rendered leading dimension must match that axis. A genuine 2D label value does
not acquire a synthetic plane axis. These decisions use the nominal
``ObjectLabelValue`` source plus declared provenance; rank alone is not an
identity authority.

Contextualizers attach source and plane context. The compiled artifact plan owns
the artifact name and type, and the runtime store owns the resulting artifact
key. A contextualizer must not rename a value, select a same-named plan, or
coerce one artifact family into another.

Artifact families without contextual image semantics inherit the root
``ArtifactType`` methods. They return their values unchanged and do not invoke
the image plane projector. Image, measurements, spatial grid, spatial graph,
and object-label artifact types override them. The artifact declaration therefore determines
projection behaviour; individual backend result classes do not need a copied
exemption registry.

Provenance invariant
--------------------

Projection cannot infer semantic slice identity from array shape. A projected
stack requires a declared runtime plane axis and complete per-slice component or
source provenance when source identity matters. Cardinality mismatches fail at
the projection boundary.

Materialized images persist that semantic metadata and their source contributors
for later workspace reconstruction. Their complete storage address is a separate
file-identity fact: it may contain a coordinate such as ``SITE`` that was needed
to name the file even when the producing operation collapsed ``SITE`` out of the
semantic projection. Reload therefore restores the persisted projection and
does not reintroduce filename coordinates as semantic provenance. Only legacy
records without persisted semantic metadata use the complete source metadata as
a compatibility fallback.

Adding a runtime value
----------------------

1. Add the nominal value type at the owning semantic boundary.
2. Add its artifact type/contract declaration if it is a new artifact family.
3. Register slice projection, aggregation, serialization, and materialization
   behavior that the value requires.
4. Add store/query and worker-transport tests.
5. Keep backend storage mechanics in PolyStore and generic array geometry and
   conversion mechanics in ArrayBridge.
