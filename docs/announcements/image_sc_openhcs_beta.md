# image.sc announcement: OpenHCS beta

This draft and its release checks record the OpenHCS 0.8.0 public-beta launch
review of 2026-08-27; they are not current release evidence. Before posting,
update the proposed release and recheck the internal launch gate at the end of
this file. The maintained release procedure is
[MCP release](../source/development/mcp_release.rst).

## Proposed title

OpenHCS 0.8.0 beta: agent-guided microscopy analysis with CellProfiler, Napari, Fiji, and OMERO

## Ready-to-paste post

Hello image.sc community,

I am announcing OpenHCS 0.8.0, the public beta of an open-source microscopy
image-analysis platform.

OpenHCS builds reproducible workflows from structured microscopy datasets. It
was designed around high-content screening and also works with structured
folders, multichannel images, Z stacks, time series, and other microscopy
batches.

The same pipeline can be edited visually, generated as Python, imported from
CellProfiler, run without the GUI, or built with an AI agent through the local
Model Context Protocol (MCP) server. Whichever route you use, the pipeline stays
visible and editable in OpenHCS. Before a run starts, OpenHCS checks the image
sources, settings, outputs, memory, and processing resources it will need.

![OpenHCS workspace with several independent assay pipelines](https://openhcsdev.github.io/openhcs/assets/gallery/multi-plate-overview.webp)

### Start with an AI agent

The Windows and macOS installers can connect OpenHCS to ChatGPT desktop, Codex,
Claude Desktop, and other supported local agent clients they detect. Launch
OpenHCS and give the agent a microscopy folder and your biological goal.

A useful starting prompt is:

> Use OpenHCS to inspect this microscopy folder and identify its samples,
> sites, channels, Z planes, and time points. Search the live function
> catalogue and draft a pipeline for my analysis goal. Compile it, explain the
> results, and show me the pipeline in OpenHCS. Ask for approval before running
> it.

The agent can inspect the source, search the live function catalogue, draft and
compile the pipeline, then run one approved sample, well, or site. It can stream
intermediate results to Napari or Fiji and inspect their ROIs and measurements.
The resulting pipeline stays editable in the GUI and as generated Python.

The website includes a short neurite outgrowth demonstration of an agent
building, compiling, running, and reviewing a pipeline through OpenHCS:

https://openhcsdev.github.io/openhcs/#mcp

The MCP server runs locally and accesses only the folders you grant it.

### Try it

Installers, gallery, and agent demonstration:

https://openhcsdev.github.io/openhcs/

For Python 3.11 to 3.13:

```bash
python -m pip install "openhcs[gui,viz,bioformats,mcp,cellprofiler-compat]"
openhcs
```

The Windows and macOS installers create an isolated desktop environment with
the GUI, MCP server, CellProfiler compatibility, Napari, Fiji, and Bio-Formats.
GPU support is optional, and Fiji resolves Java on first use. The installers
are not yet signed or notarized, so Windows or macOS may ask you to confirm that
you want to run them.

### CellProfiler interoperability

Supported CellProfiler `.cppipe` files can be imported through the GUI or
Python. The importer translates familiar images, objects, measurements,
relationships, and export modules into the same editable pipeline used
throughout OpenHCS.

Automated tests import, compile, run, and compare outputs for 30 pipelines from
CellProfiler examples, tutorials, and benchmark supplements. I would like to
expand this set using community workflows.

### Inspect intermediate results in Napari and Fiji

Enable streaming on any pipeline step to review intermediate processing during
a run. Napari displays images, Shapes ROIs, and measurement tables; selecting a
row highlights its ROI and navigates to the corresponding Z plane. Fiji
receives the matching image plane and ROI Manager entries. Both viewers run in
separate processes.

See both viewer workflows in the gallery:

https://openhcsdev.github.io/openhcs/#gallery

### Experimental OMERO integration for facility operators

OpenHCS can use images and metadata from OMERO as pipeline inputs and store
derived results through OMERO. This integration is experimental and is aimed at
imaging facilities and shared infrastructure.

I would value feedback about deployment, permissions, shared execution, result
publication, and the handoff between an imaging facility and its users.

### Additional capabilities

- ImageXpress, Opera Phenix, Bio-Formats, structured-folder, and OMERO sources;
- mapping of samples, wells, sites, channels, Z, and time from microscope
  metadata or custom filename layouts;
- CPU multiprocessing and optional GPU processing;
- images, object labels, measurements, relationships, tables, spatial graphs,
  ROIs, and files as pipeline results.

Each processing function determines whether it works plane by plane or across a
volume. Current 3D routes include Watershed segmentation and object intensity,
size, shape, and occupied-volume measurements. Plane-by-plane functions keep
objects separate between Z planes.

### Links

[Documentation](https://openhcs.readthedocs.io/) |
[Source and issues](https://github.com/OpenHCSDev/OpenHCS)

### Feedback I am looking for

Please try OpenHCS, especially the MCP workflow, and tell me what worked, what
was confusing, or what broke. I am especially interested in:

- source layouts, image axes, and CellProfiler imports;
- Napari, Fiji, ROI, and OMERO workflows;
- installation and first-run experience.

Synthetic or redacted examples are welcome.

If OpenHCS proves useful for your work, please share it with colleagues who
might benefit from it.

OpenHCS is MIT licensed. Thanks for taking a look.

## Internal launch gate - exclude from the post

### Public release boundary recorded on 2026-08-27

- Public package and installer release at that review: `0.8.0`, tag commit
  `af0341065b2edf9bf4b0752ec74e47ac85433c7d`.
- Current source main at the time of this review:
  `b98361c9141976454c82716564f94a1b0c2794b1`.
- Every user-facing capability in the post is present in `0.8.0`.

### Verified on 2026-08-27

- [x] PyPI exposes active `0.8.0` wheel and source distributions.
- [x] The public GitHub Release is published, marked latest, and contains direct
      Windows EXE and macOS DMG installer assets.
- [x] Both latest-installer links return HTTP 200.
- [x] The MCP Registry marks `io.github.OpenHCSDev/openhcs` version `0.8.0`
      latest and pins `openhcs[gui,mcp,viz]==0.8.0`.
- [x] The release-tag Integration Tests and PyPI publication workflows passed.
- [x] The current Website and repository Documentation workflows passed.
- [x] Read the Docs `latest` displays `0.8.0`.
- [x] Every linked website, documentation, media, release, and evidence asset
      returns HTTP 200.
- [x] Gallery media derives from real application or viewer captures and has a
      published capture/checksum record.
- [x] The agent showcase is accompanied by the uncut recording and
      machine-readable evidence, and its post-run replay is labelled.
- [x] The public release canary passed on Linux, macOS, and Windows.
- [x] The latest `main` Integration Tests workflow completed successfully with
      all 39 jobs passing.
- [ ] Preview the ready-to-paste section in the image.sc composer and confirm
      that the screenshot is legible at the forum's rendered width.
- [ ] Recheck the public package, latest release, installer links, MCP Registry,
      and website immediately before submitting the post.

### Posting plan

1. Recheck the public release endpoints and current green CI immediately before
   posting.
2. Paste only the proposed title and ready-to-paste post into image.sc.
3. Preview the post on desktop and mobile widths. Remove the embedded
   screenshot if it is too dense at the forum's rendered width. Keep the
   gallery as the visual entry point.
4. Post and step away. Read and answer replies when rested.
5. Triage replies into installation friction, source-layout support,
   CellProfiler compatibility, dimensionality/measurement needs, and general
   usability. Ask for a synthetic or redacted representative before requesting
   private data.

Keep architecture and feature scope frozen through the announcement. Pause for
a newly discovered release-blocking installation or data-integrity failure.
