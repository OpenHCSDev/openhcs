---
bibliography: ../openhcs_references.json
csl: ../styles/elsevier-vancouver.csl
link-bibliography: true
link-citations: true
reference-section-title: References
---


## Supp. Table 4. User tasks covered by automated software checks {#supplementary-table-4.-user-tasks-covered-by-automated-software-checks}

The automated checks connect software changes to expected user outcomes. The table distinguishes complete analysis or service runs from focused component checks and lists their configured environments. We provide completed output comparisons in [Supp. Data 2](analysis_records.md#supplementary-data-2-cellprofiler-workflow-comparison) and a passed, revision-pinned component-test run in [Data 8](analysis_records.md#supplementary-data-8-workflow-regression-tests). The [test-workflow definition](https://github.com/OpenHCSDev/openhcs/blob/3fea2bb30142aa76ef25fb60120579b2db58d65e/.github/workflows/integration-tests.yml) specifies the configured coverage below, rather than a result for every environment.

| User task | Expected outcome checked | Check and configured environment |
|:--------------------|:----------------------------------|:-------------------------------------------|
| [Reuse a CellProfiler pipeline](https://github.com/OpenHCSDev/openhcs/blob/0d4954e57268ebbe4c84c028de94b5725fd95990/tests/integration/test_cellprofiler_official30_zmq.py#L525-L535) | Execute 30 imported pipelines and compare their outputs with retained native image and measurement references. | Configured: complete pipeline runs on Linux, Windows and macOS, each with Python 3.12 and 3.14. Recorded output comparisons: [30-workflow results and tested environments](analysis_records.md#supplementary-data-2-cellprofiler-workflow-comparison). |
| [Inspect processing results in Fiji and napari](https://github.com/OpenHCSDev/openhcs/blob/0d4954e57268ebbe4c84c028de94b5725fd95990/tests/integration/test_cellprofiler_official30_zmq.py#L720-L815) | Check that a fresh Fiji process contains images and that napari reports the expected live state after processing. | Real viewer processes: one colocalization workflow with Fiji alone and with Fiji plus napari; Linux, Python 3.12. |
| [Process images from files or Zarr](https://github.com/OpenHCSDev/openhcs/blob/0d4954e57268ebbe4c84c028de94b5725fd95990/tests/integration/test_main.py#L822-L901) | Read generated microscope inputs, execute processing and check output directories and structured metadata. | Synthetic-image integration: disk and Zarr with ImageXpress and Opera Phenix layouts; Linux, Windows and macOS, Python 3.12. |
| [Process images held in OMERO](https://github.com/OpenHCSDev/openhcs/blob/0d4954e57268ebbe4c84c028de94b5725fd95990/tests/integration/helpers/fixture_utils.py#L363-L431) | Upload generated images to an OMERO service and execute the analysis on its plate. | Real service integration: Linux, Python 3.11 and 3.12. This checks server-backed execution, not filesystem-export equivalence. |
| [Save and reload analysis settings as Python](https://github.com/OpenHCSDev/openhcs/blob/0d4954e57268ebbe4c84c028de94b5725fd95990/tests/unit/test_pycodify_formatters.py) | Reconstruct selected settings from generated Python and compare their values, including defaults and local changes. | Configured: component round-trip checks with substituted definition metadata; Linux, Python 3.12. Recorded separately: [passed Python-generation tests at revision 7a7d21f](analysis_records.md#supplementary-data-8-workflow-regression-tests). |
| [Connect compatible processing steps](https://github.com/OpenHCSDev/openhcs/blob/0d4954e57268ebbe4c84c028de94b5725fd95990/tests/unit/test_funcstep_contract_validator.py#L432-L472) | Reject incompatible image-stack inputs before execution. | Configured: component validation checks; Linux, Python 3.12. Recorded separately: [passed function-validation tests at revision 7a7d21f](analysis_records.md#supplementary-data-8-workflow-regression-tests). |
| [Select processing functions from current descriptions](https://github.com/OpenHCSDev/openhcs/blob/0d4954e57268ebbe4c84c028de94b5725fd95990/tests/unit/test_function_catalog_zmq.py#L720-L740) | Reject a request based on an outdated function catalogue. | Configured: component request-routing check with a substituted catalogue service; Linux, Python 3.12. Recorded separately: [passed catalogue-revision tests at revision 7a7d21f](analysis_records.md#supplementary-data-8-workflow-regression-tests). |

