# Edit this pipeline and save to apply changes

from openhcs.processing.presets.mfd_specs import MFD_STITCH_ASHLAR_CPU, build_mfd_preset

pipeline_steps = build_mfd_preset(MFD_STITCH_ASHLAR_CPU)
