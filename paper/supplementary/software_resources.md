---
bibliography: ../openhcs_references.json
csl: ../styles/elsevier-vancouver.csl
---

# Software ecosystems and project-hosted learning resources

## Development history and extension interfaces

Release dates and first descriptions are distinguished below; they are not interchangeable measures of a project's age.

| Platform | Release or description | Implementation and extension route |
| --- | --- | --- |
| ImageJ / Fiji | ImageJ released in 1997; Fiji first released in 2007. | Java-based ImageJ supports plugins and macros; Fiji packages ImageJ with community plugins and an updater [@Schneider2012; @Schindelin2012]. |
| CellProfiler | Released in 2005; first described in 2006. | Configurable analysis modules; the later Python implementation also supports plugin modules [@Carpenter2006; @McQuin2018; @Weisbart2024]. |
| Icy | Introduced in 2011. | Java plugins, scripting and graphical workflows [@deChaumont2011; @deChaumont2012]. |
| napari | First minor release in 2019. | Python viewing and analysis; plugin packages add readers, writers and interactive tools [@NapariRelease2019; @NapariPlugins]. |
| PyImageJ | Described in 2022. | Connects Java-based ImageJ and Python within a Python process; napari-imagej uses this bridge within napari [@Rueden2022PyImageJ; @NapariImageJ]. |
| OMERO | Data-management system described in 2012. | Shared image storage, metadata management and access from analysis tools [@Allan2012]. |
| BioImageIT | Described in 2022. | Links image-data management with analysis tools and packaged processing environments [@Prigent2022]. |

## Resource inventory

Web inventories were inspected on 15 October 2026. Each entry counts the collection named by its link. Plugins, tutorial pages, script files and complete workflows are separate units; project-hosted collections include community contributions.

| Platform | Extensions | Tutorials and training | Scripts and workflows |
| --- | --- | --- | --- |
| ImageJ / Fiji | >500 plugins reported in 2012 [@Schneider2012]; historical count. | 26 pages under “Tutorials on this site” in the [index](https://imagej.net/tutorials/). | 402 top-level macro/script files in the [archive](https://imagej.net/ij/macros/). |
| CellProfiler | 24 [supported plugins](https://plugins.cellprofiler.org/supported_plugins.html); >90 built-in modules reported separately [@Weisbart2024]. | 10 main [tutorial exercises](https://tutorials.cellprofiler.org/). | 16 [application collections](https://cellprofiler.org/examples), each potentially containing multiple pipelines. |
| Icy | 448 [plugins](https://icy.bioimageanalysis.org/plugins/) [@IcyCatalogue]. | 6 project-produced [training PDFs](https://icy.bioimageanalysis.org/trainings/), including a shortcut reference. | 82 [scripts](https://icy.bioimageanalysis.org/scripts/); 87 [graphical protocols](https://icy.bioimageanalysis.org/protocols/). |
| napari | 680 plugins in the [dashboard](https://napari.org/weather-report/) [@NapariDashboard]. | 4 worked tutorials in the [index](https://napari.org/stable/tutorials/index.html). | 115 examples in the [code gallery](https://napari.org/stable/gallery.html). |
| BioImageIT | [Python tools](https://bioimageit.readthedocs.io/en/stable/documentation/tool_integration.html) with declared dependencies and environments; total not established. | 2 worked tutorials in the [documentation index](https://bioimageit.readthedocs.io/en/latest/documentation/documentation.html). | No separate total established from the inspected index. |

### Counting rules

Tutorial counts exclude navigation links, translations of the same exercise, linked external courses, how-to sections and video playlists. The CellProfiler count runs from beginner segmentation through UnmixColors, excluding bonus material, profiling resources and older-version tutorials. ImageJ archive counts use unique top-level filenames ending in `.txt`, `.ijm` or `.js`, excluding `AA_ReadMe.txt`, subdirectories and ZIP bundles; a file can contain several macros. Napari examples are unique `gallery/*.html` destinations. Icy uses its catalogue totals and the six PDFs under “Our own course and tutorial,” not six equivalent tutorials. An unestablished count is not zero.

### Community support

Rueden et al. reported approximately 10,000 image.sc users and more than 15,000 posts per year in 2019 [@Rueden2019Forum]. Ouyang et al.'s 2023 sample found installation mentioned in 9.9% of opening posts and approximately 19% of roughly 500 threads [@Ouyang2023]. Napari's dashboard reported 1,460 tagged topics and 938 participating users on 15 October 2026 [@NapariDashboard]. Posts count individual messages; topics count discussion threads. These totals describe community activity across bugs, usage questions, integration requests and announcements; they do not supply comparable per-platform counts for each category.
