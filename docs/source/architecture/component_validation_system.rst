Component validation
====================

Component declarations describe semantic microscope dimensions such as well,
site, channel, Z, and time point. Each is an ``Axis`` class declared by the
active ``AxisFamily``; subsets such as the variable axes are family queries,
and a step's absent grouping is the explicit ``Ungrouped`` declaration.

Validation decodes external names through ``AxisFamily.named`` and rejects
unknown or semantically invalid combinations. It checks, among other things,
that:

- configured variable components exist in the source universe;
- grouping is allowed by every callable contract in the pattern;
- required callable axes are present;
- sequential and multiprocessing axes do not create an invalid execution
  topology.

Consumers should use the shared conversion/validation helpers and nominal enum
members. They must not maintain copied component-name sets. See
:doc:`../concepts/data_dimensions` and :doc:`processing_semantics`.

