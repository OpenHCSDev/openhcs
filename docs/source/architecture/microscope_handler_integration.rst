Dataset source integration
==========================

``DatasetSource`` is the nominal root for format-specific dataset behaviour.
Concrete sources self-register through ``AutoRegisterMeta`` under their
``source_name``. The registry discovers the kernel's own members in
``openhcs.core.dataset_sources`` and then imports the modules the active
``AxisFamily`` lists in ``extension_modules``; for microscopy these include
``openhcs.microscopes``. The kernel never imports a domain module by name.

Owned declarations
------------------

A source owns:

- its ``source_name`` identity, selection role, and detection behaviour;
- filename parsing and metadata-handler type;
- virtual-workspace root and source projection;
- compatible storage backends;
- viewer metadata required for axis-aware display.

The registry is the source of truth. Generic discovery, compiler, and UI code
iterate ``DatasetSource.__registry__`` or ``DatasetSourceChoice.choices()``.
They must not maintain a copied source list or import concrete source modules
to inspect names.

Selection
---------

``PipelineConfig.dataset_source`` holds a ``DatasetSourceChoice`` class:
``AutoDetectedSource`` (spelled ``auto``) or one registered source. Boundaries
spell the choice by ``source_name``. Automatic detection walks
``DatasetSource.detection_order()``: prepared OpenHCS workspaces first, then
sources ranked by their selection-role mixin. Selection roles such as
``FormatSpecificSource``, ``DeclaredFileSource``, and
``PreparedWorkspaceSource`` are capability mixins on the source class.

``DatasetSourceChoice.open`` resolves the source class, lets declared source
bindings select the declared-file source when the role allows it, constructs
the leaf through its ``create`` hook, and binds ``dataset_root`` uniformly.
Leaf-specific initialisation belongs on that leaf's ``create`` hook; the opener
does not dispatch on concrete source names.

Source and compiler boundary
----------------------------

After initialisation, the source supplies dataset metadata and source files to
the source-workspace projection. The compiler uses that projection to construct
source universes, execution-axis values, main-flow dependencies, and named
source bindings. PolyStore owns the underlying references, virtual paths, and
backend I/O.

A source may use a decoder-owned metadata handler while discovering exact
source planes. Once it persists the virtual workspace, its active
``metadata_handler`` becomes the workspace metadata owner. Consumers therefore
read one post-initialisation metadata handler instead of conditionally
combining raw store coordinates with projected workspace coordinates.

``MetadataHandler.component_value_set()`` returns one complete
``MetadataComponentValueSet`` keyed by the axes of the active ``AxisFamily``.
Metadata handlers implement that single projection; generic consumers iterate
the family instead of calling one method per concrete axis. Viewer and
serialized mappings receive string keys only at their explicit boundary.

The persisted workspace records the ``source_name`` of the source that produced
its backing references. When the workspace is reopened, that registered source
class re-registers its decoder backends together with the dataset-specific
virtual-workspace backend. Replay therefore follows the recorded declaration
without reconstructing a configuration-dependent ingestion instance or
requiring the ``SourceBindingsConfig`` used at ingestion.

Extension boundary
------------------

A new format integration is a registered ``DatasetSource`` leaf, in a module
listed by the active family's ``extension_modules``, with its parser, metadata
handler, identity, selection role, and backend compatibility at the owning
module. Dataset-specific ordinary-file layouts whose selection and axes can be
declared with ``SourceBindingsConfig`` use the source-binding source
(``source_bindings``); the dataset name is not registered as a source.
Generic discovery and compilation consume the resulting declaration.
The task-oriented procedure and required tests are in
:doc:`../development/source_binding_extension`; the ownership rule is expanded
in :doc:`nominal_ownership`.
