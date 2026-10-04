# P5: Conversions planned across steps

**Index:** [README.md](README.md). **Last; coordinate with S4's owner.**

## What is wrong

`convert_memory` (from `openhcs.core.memory`) runs per function call in `execute` (`openhcs/core/steps/function_runtime.py:1058`), converting from the payload's memory type to the callable's. Consecutive steps on the same device can convert data away and back, and the decision is made per call, though the whole step sequence and every step's memory types are known when the pipeline compiles.

## Target

The compiler plans memory placement across the step sequence: a conversion is scheduled only where consecutive steps' memory types differ, and data stays on the GPU across consecutive GPU steps. The compiled invocation (P1) carries whether its input needs converting, and the runtime never decides it per call.

## Done when

Converting between memory types happens only at planned boundaries, and P0's profile shows conversion time before and after on a pipeline that mixes CPU and GPU steps.
