Component validation
====================

Component declarations describe the data's dimensions; the microscopy family
declares well, site, channel, Z, and time point. Each is an ``Axis`` class
declared by the active ``AxisFamily``; subsets such as the variable axes are
family queries, and a step's absent grouping is the explicit ``Ungrouped``
declaration.

Validation decodes external names through ``AxisFamily.named`` and rejects
unknown or semantically invalid combinations. It checks, among other things,
that:

- a step's variable and grouping axes are variable axes of the family (every
  axis but the partition axis), and the grouping axis is not also a variable
  axis;
- dictionary-pattern keys exist among the dataset's values for the grouping
  axis;
- grouping is allowed by every callable contract in the pattern;
- the step's variable axes cover every axis role a callable requires;
- no pipeline sequential axis is also a step's variable axis.

Consumers should use the shared validation helpers and the axis classes
themselves. They must not maintain copied component-name sets. See
:doc:`../concepts/data_dimensions` and :doc:`processing_semantics`.

