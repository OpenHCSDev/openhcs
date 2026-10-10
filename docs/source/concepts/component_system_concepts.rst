Component identities
====================

Components name the semantic dimensions of a dataset. For microscopy they are
well, site, channel, Z index, and timepoint. Each is a declared axis: a class
nested in the domain's axis family, which the domain activates once per process.

Axes, families, and roles
-------------------------

``Axis``
  One declared dimension. The class is its identity; ``Axis.name`` is its
  spelling at external boundaries (wire payloads, filenames, metadata, MCP).

``AxisFamily``
  A domain's ordered set of axes. Microscopy declares ``Microscopy`` in
  ``openhcs.domains.microscopy.axes``; the kernel asks only
  ``AxisFamily.active()``.

Roles
  Capability mixins an axis carries: ``PartitionAxis`` (exactly one; the
  parallel axis), ``TileAxis``, ``ColourAxis``, ``StackAxis``, ``TimeAxis``,
  ``DefaultVariable`` and ``DefaultGroupBy``. Kernel code selects axes by role,
  for example ``AxisFamily.active().with_role(StackAxis)``, never by member.

``Ungrouped``
  The explicit absent-grouping declaration a step's ``group_by`` may hold.

Partition axis
--------------

The partition axis (normally well) partitions orchestrator work. The compiler
creates a context for every selected value on this axis. Every other axis is a
variable axis that a step may assemble, group, or sequence along.

Stack and grouping use
----------------------

.. code-block:: python

   from openhcs.core.config import LazyProcessingConfig, ProcessingConfig
   from openhcs.domains.microscopy.axes import Microscopy

   processing = ProcessingConfig(
       variable_components=(Microscopy.Site,),
       group_by=Microscopy.Channel,
   )
   step = FunctionStep(
       func={"1": nuclei, "2": neurites},
       processing_config=LazyProcessingConfig.from_config(processing),
   )

Site declares the stack axis. Channel partitions those site stacks for
dictionary routing. ``ProcessingContract`` separately declares whether each
callable has per-plane or whole-stack semantics.

Runtime scope
-------------

Compiled group identity is represented by ``ComponentGroupScope`` and runtime
artifact keys use ``RuntimeExecutionAxisScope``. Component identity is not
recovered from path text at runtime.

Extension rule
--------------

A new domain declares one ``AxisFamily`` subclass and activates it. Do not
create copied component lists or name family members in compiler, UI,
storage, or backend code; ask the active family by role.

See :doc:`data_dimensions` and
:doc:`../architecture/processing_semantics`.
