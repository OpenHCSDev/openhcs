Automatic dtype conversion
==========================

``DtypeConfig`` controls how decorated callables reconcile input and output
dtypes. The setting is inherited through pipeline and step ObjectState scopes
and is resolved during compilation.

The two primary policies are:

``NATIVE_OUTPUT``
  Keep the callable/framework's native output dtype without intensity scaling.

``PRESERVE_INPUT``
  Convert the result back toward the input dtype using ArrayBridge's declared
  conversion policy.

In **Global Configuration**, open **Dtype Config** and set **Default Dtype
Conversion** to choose the application default. To override one pipeline or
step, open its configuration, expand **Dtype Config**, and set the same field at
that narrower scope. Leave the lazy field unset to inherit the broader value.

To change one callable within a chained or channel-grouped step, include its
``dtype_config`` in that callable's kwargs using code mode. That explicit
override is retained when switching between the code and form views.

The equivalent step declaration is:

.. code-block:: python

   from openhcs.core.config import LazyDtypeConfig
   from arraybridge.decorators import DtypeConversion

   step.dtype_config = LazyDtypeConfig(
       default_dtype_conversion=DtypeConversion.PRESERVE_INPUT,
   )

Save an 8-bit visualisation
---------------------------

For a display image that does not need its original precision, set ``UINT8``
on the image-producing callable in the function pattern and materialise that
step's result:

.. code-block:: python

   from openhcs.core.config import LazyDtypeConfig, LazyStepMaterializationConfig
   from openhcs.core.steps.function_step import FunctionStep
   from openhcs.processing.backends.processors.numpy_processor import create_projection
   from arraybridge.decorators import DtypeConversion

   preview_step = FunctionStep(
       func=(
           create_projection,
           {
               "dtype_config": LazyDtypeConfig(
                   default_dtype_conversion=DtypeConversion.UINT8,
               ),
           },
       ),
       name="8-bit projection for review",
       step_materialization_config=LazyStepMaterializationConfig(enabled=True),
   )

Use this example with a floating-point image stack. The callable-level policy
converts the main result before materialisation. When TIFF is the selected
output format, the disk file therefore contains 8-bit pixels.
The policy belongs to this callable occurrence, not to every function in the
pipeline. Later steps using this result also receive its 8-bit values, so keep
the conversion on a terminal review route if analysis still needs full
precision.

Check the values before choosing this policy. For NumPy-backed callables,
float-to-``UINT8`` conversion scales the minimum and maximum of each
non-constant callable result to the 8-bit range. Integer-to-``UINT8``
conversion casts instead: values outside 0--255 can wrap. Neither is suitable
for preserving quantitative intensities or object-label identities. A
tuple-returning callable converts only its first, main result; it does not
convert auxiliary named outputs.

To save space without changing pixel values, use lossless disk TIFF compression
instead. See :doc:`../concepts/storage_system` for the separate storage policy.

Compile again after changing the policy. Do not cast merely to cross
NumPy/CuPy/Torch boundaries; memory conversion and dtype policy are separate
declarations.

ArrayBridge owns generic dtype conversion behavior. OpenHCS records the resolved
configuration in the callable/runtime plan. See
:doc:`../concepts/dtype_config_system` for the policy boundary and
:doc:`../guides/memory_type_integration` for framework conversion.
