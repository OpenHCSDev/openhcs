# Authoring and preview release review, 2026-09-10 UTC

Scope: the 55 authority-drift findings reported for candidate
`ba3bf4d1f768b11b71a3f4458bf1a4491a3047a3`, covering 47 documentation records,
plus the two code/UI pages updated to explain the changed behaviour. This is
review evidence, not another product specification.

## Source comparison

The affected pages, including the project README, were read completely. The
review compared the changes since the preceding release with each page's
claims and recorded authority roles:

- `UIConfig.list_previews` embeds the generic formatting declaration. The main
  window supplies it to both managers at startup and on save; persistence uses
  the existing configuration transaction. The new display policy does not
  change processing, endpoint ownership, logging, analysis, or window identity.
- The generic manager applies formatting and wrapping together. Collection
  previews are bounded and can be expanded; field selection and abbreviations
  remain declaration-owned. The configuration reference already derives its
  fields from those declarations, so no second option table was added.
- Function parameter projection follows signature order in clean and full
  views. Extra supplied parameters retain their relative order. Equality
  remains caller-owned, and missing parameters are not inserted.
- Step code uses the existing function-pattern reconciliation path. Once a
  child parameter state exists, exports read that state's current values,
  including hidden groups. Step Save and pipeline-apply baseline semantics
  remain distinct. Numeric text uses the generic locale-aware control without
  reducing configured precision.
- Flash registration cleanup now uses a Qt-owned receiver and slot for the
  native sender lifetime. The OpenHCS transition page remains a link to the
  generic package owner rather than copying its implementation.
- The package changes raise the python-introspect and pyqt-reactive minimum
  versions and project OpenHCS 0.8.5 into release metadata. Extras, Python
  support, entry points, package ownership, and installation procedures are
  unchanged by those dependency/version edits.
- The release agent's final Black changes affect only three regression-test
  files. Their current contents, rather than pre-formatting hashes, are used
  in the updated records.

## Editorial changes

Reference pages now identify list-preview presentation without duplicating the
generated field reference. The desktop reference explains its two-panel scope.
The code-editing how-to tells users what they will see after applying a step
edit; the architecture explanation records the owner and state relationships.
Generic transition pages retain their existing ownership links.

Updated prose:

- `docs/source/architecture/list_item_preview_system.rst`
- `docs/source/architecture/ui_services_architecture.rst`
- `docs/source/architecture/code_ui_interconversion.rst`
- `docs/source/guide_for_biologists/basic_interface.rst`
- `docs/source/reference/configuration.rst`
- `docs/source/user_guide/code_ui_editing.rst`

## Validation

- OpenHCS focused regressions: 54 passed, covering real step widgets and child
  states, grouped/list transitions, hidden-group export, signature ordering,
  configuration propagation/persistence, and compact source-binding previews.
- pyqt-reactive focused regressions: 77 passed, covering numeric round trips,
  preview formatting/wrapping, and native Qt destruction lifetime.
- The release agent's warning-fatal fresh OpenHCS Sphinx build passed with the
  updated prose at `/tmp/openhcs-authoring-docs`; CI additionally rebuilds the
  first-party inventories from its recorded source candidates.
- Review hashes are refreshed only for the compared authorities and edited
  pages. The existing `scripts/validate_docs.py` remains the acceptance gate.
- Final documentation validation passed: 156 files, 24 Python blocks and 155
  audited documentation sources. The documentation diff has no whitespace errors.

Commands:

```sh
QT_QPA_PLATFORM=offscreen .venv/bin/python -m pytest -o addopts='' -n 4 --dist loadfile tests/unit/pyqt_gui/test_step_code_widget_roundtrip.py tests/unit/pyqt_gui/test_main_config_propagation.py tests/unit/pyqt_gui/test_ui_config_lifecycle.py tests/unit/pyqt_gui/test_source_binding_preview_policy.py tests/unit/test_pycodify_formatters.py -q

# From external/pyqt-reactive, using the OpenHCS environment:
QT_QPA_PLATFORM=offscreen /home/ts/code/projects/openhcs/.venv/bin/python -m pytest -o addopts='' -n 4 --dist loadfile tests/test_numeric_roundtrip.py tests/test_list_preview_wrapping.py tests/test_preview_formatters.py tests/test_flash_destruction_lifetime.py -q

python scripts/validate_docs.py docs/source
```
