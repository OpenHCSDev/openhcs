# Interpret raw microscopy images before analysis

This reference adapts Pete Bankhead's *Introduction to Bioimage Analysis*, as
packaged by Agentic-J's `bioimage_course` at
[`7f3e1f0`](https://github.com/MMV-Lab/Agentic-J/tree/7f3e1f0888cd06f22ebdfb5cf1fc43d0e7769a67/skills/bioimage_course).
The course records book source `a017bbc2656a747ab3c87e5d721e9897881ed4c2`
and [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/) attribution to
Pete Bankhead. The operational checks here are a condensed OpenHCS adaptation,
not a copy of the course's worked answers or a validated assay recipe.

## Channel identity and biological interpretation

A scientific channel is an acquired intensity plane; its display colour is a
presentation choice. A green layer need not be the cell-body stain, and a bright
compact focus need not be a whole cell. Acquisition channel names, staining
information and the same-coordinate raw morphology together support identity.
Do not infer that the physical source has one channel from a one-channel export.

An RGB screenshot or rendered composite may combine stains, clip values and
discard bit-depth or axes. Splitting its R/G/B components does not recover the
original acquired channels. Retain the scientific source with metadata. For
brightfield colour stains, a stain-specific colour model is different from
selecting the brightest RGB component; its assumptions must match the task.

Compare each candidate channel at whole-field, regional and native-object scale.
Look for compartment shape and supported boundaries: compact nuclear material,
extended cytoplasm, continuous processes or puncta inside larger structures.
Inspect central and edge regions, bright and dim signal, sparse and crowded
regions. Form a provisional target hypothesis, retain ambiguities, and seek
metadata rather than silently treating a display colour as a stain identity.

## Display windows, histograms and saturation

A display window maps intensities to brightness; changing its limits does not
change the scientific pixels unless an analytical transform is explicitly run.
Compare a faint-preserving and a local-detail window at the same coordinates.
An object absent under one window may be supported under another.

Compare bounded raw histograms and local backgrounds, not just an attractive
thumbnail. A high-percentile bright object can dominate auto-contrast without
representing the ordinary field. A peak at the detector's effective maximum can
indicate saturation; inspect numeric values and acquisition metadata rather
than assuming every white pixel is saturated. Saturated acquisition has lost
intensity distinctions that contrast adjustment cannot restore.

Per-image auto-stretch can make unequal exposures look equal, or comparable
signal look unequal. Quantitative comparisons require numeric measurement
images and acquisition controls; representative comparison figures need a
documented shared display mapping. Display gamma and analytical gamma are
different operations with different provenance.

## Dtype and numeric range

Storage type is not the effective detector range: a 16-bit TIFF can contain
12-bit values. Record the dtype and observed range before borrowing a threshold
from an 8-bit example. An unsigned subtraction may underflow; float processing
can preserve negative and fractional values. Clipping, rescaling and converting
to RGB can destroy quantitative information. Labels are integer identities,
not intensities; stretching or interpolating label values can corrupt them.

## Axes, spacing and geometry

Verify which dimensions mean channel, Z, time and site. A stack is not evidence
of a Z-volume, and a montage is not a physical coordinate system until its
spacing and transforms are known. Check XY spacing, Z spacing and units; do not
invent a physical calibration from the TIFF extension or apparent cell size.
If calibration is absent, report pixel-based quantities as such.

A maximum projection can merge objects separated in Z and inflate overlap;
it cannot establish 3-D counts or physical volume. A 2-D callable applied to
every Z plane can count one nucleus repeatedly. Before comparing raw and result,
check source/component identity, scale, translation and the selected axes.

## Sources

- Bankhead: [Images & pixels](https://bioimagebook.github.io/chapters/1-concepts/1-images_and_pixels/images_and_pixels.html), [Measurements & histograms](https://bioimagebook.github.io/chapters/1-concepts/2-measurements/measurements.html), [Types & bit-depths](https://bioimagebook.github.io/chapters/1-concepts/3-bit_depths/bit_depths.html).
- Bankhead: [Channels & colours](https://bioimagebook.github.io/chapters/1-concepts/4-colors/colors.html), [Pixel size & dimensions](https://bioimagebook.github.io/chapters/1-concepts/5-pixel_size/pixel_size.html), [Files & file formats](https://bioimagebook.github.io/chapters/1-concepts/6-files/files.html).
