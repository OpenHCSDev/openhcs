"""A new declaration and independent cooperative capability need no consumer edits."""

import pytest

from openhcs.interop.cellprofiler.parser import ModuleBlock, ModuleSetting
from openhcs.interop.cellprofiler.settings_binder import (
    ModuleOnlySettingBinding, SettingToKeywordBinding, SettingsBinder,
)


class RecordingBindingCapability(SettingToKeywordBinding):
    def bind(self, module, kwargs, binder):
        binder.events.append(("before", self.setting_name))
        super().bind(module, kwargs, binder)
        binder.events.append(("after", self.setting_name))


class RetainedSelectorWithRecording(RecordingBindingCapability, ModuleOnlySettingBinding):
    pass


class RecordingRetainedSelector(ModuleOnlySettingBinding, RecordingBindingCapability):
    pass


@pytest.mark.parametrize("declaration", [RetainedSelectorWithRecording, RecordingRetainedSelector])
def test_new_module_only_selector_uses_original_reconstruction_and_cooperative_bind(declaration):
    binding = declaration("An independent inactive selector")
    (record,) = binding.records_from_kwargs({binding.require_parameter_name(): "UnloadedSource"})
    module = ModuleBlock("Synthetic", 1, setting_records=[record])
    binder = SettingsBinder()
    binder.events = []
    assert binder.bind_declared(module, (binding,)) == {}
    assert record == ModuleSetting("An independent inactive selector", "UnloadedSource")
    assert not binding.declares_artifact
    assert binder.events == [
        ("before", binding.setting_name), ("after", binding.setting_name),
    ]
    assert declaration.__mro__.index(RecordingBindingCapability) < declaration.__mro__.index(SettingToKeywordBinding)


def test_original_runtime_setting_still_binds_its_parsed_value():
    module = ModuleBlock("Synthetic", 1, setting_records=[ModuleSetting("Divisor", "2")])
    assert SettingsBinder().bind_declared(module, (SettingToKeywordBinding("Divisor"),)) == {"divisor": 2}
