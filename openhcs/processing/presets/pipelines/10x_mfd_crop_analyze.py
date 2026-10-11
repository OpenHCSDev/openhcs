# Edit this pipeline and save to apply changes

from openhcs.processing.presets.mfd_specs import MFD_CROP_ANALYZE, build_mfd_preset

pipeline_steps = build_mfd_preset(MFD_CROP_ANALYZE)
