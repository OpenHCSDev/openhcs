# Independent agent-authored assay validation

## Prospective design

Three public Broad Bioimage Benchmark Collection (BBBC) assays were prepared
before pipeline authoring. Each authoring trial received only a bounded
development image set, the biological task, channel identities, the permitted
OpenHCS desktop and MCP endpoints, and an output directory. Reference
annotations, treatment metadata, held-out images, evaluation code, earlier
trial pipelines and repository source were withheld. A fresh `gpt-5.6-sol`
agent used registered OpenHCS functions through the connected desktop. The
development pipeline was frozen before the held-out path was disclosed. The
held-out run could change the input and output roots but not the scientific
functions or parameters.

The prepared corpus manifest binds every source archive member, converted
image, split assignment and evaluation artifact. Its SHA-256 digest is
`2264276b0e7d9e905c498136333f6dab49f6ff1c059ce44db7815eb2d3b7096d`.
Prediction manifests were frozen before the evaluator opened any held-out
annotation. These are single prospective authoring attempts, not repeated-trial
estimates of agent reliability.

## BBBC039 nuclear instance segmentation

BBBC039 contains Hoechst images of U2OS nuclei from a chemical screen and
independent instance annotations. Four fields from the official validation
partition were available during development; all 50 official test fields were
held out. The agent selected a registered primary-object segmentation function
and retained integer label images, ROI archives and per-object measurements.
The exact development pipeline was then executed on the test partition.

The frozen held-out output contains 250 artifacts and 6,964 predicted nuclei.
At one-to-one instance matching with intersection over union at least 0.5,
4,733 of 5,720 reference nuclei matched. Pooled precision was 0.6796, recall
was 0.8274 and object F1 was 0.7463; mean field object F1 was 0.7360 and mean
field foreground Dice was 0.9348. Predicted count exceeded reference count by
1,244. The overlap diagnostic found 1,598 reference instances intersecting at
least two predictions by at least 10%, compared with 155 predictions
intersecting at least two reference instances. The first blind pipeline
therefore recovered foreground well but over-segmented nuclear instances.

The prediction manifest contains 250 entries and has SHA-256 digest
`1e20a75889b562eb1e3ab8333f7a350b7c1a60f65dbc1ce3f3e8b6120c144fc3`.
The typed score receipt has SHA-256 digest
`901e925f977cfe6ef470c0199bc50dcb477a69dc78f9aac1e05d5acd4e7df288`.

## BBBC007 nuclear and cell segmentation

BBBC007 contains paired DNA and actin images of Drosophila Kc167 cells with
manual nuclear and cell outlines. Four hash-selected fields were available for
development and the remaining 12 were held out. The agent authored a two-step
pipeline that identified nuclei from DNA and propagated those objects into the
actin channel. The held-out run retained 96 artifacts: primary and secondary
label images, ROI archives, segmentation summaries and per-object tables.

Across the held-out fields, the manual outlines enclosed 1,082 closed nuclear
interiors and contained 12 open or frame-connected regions that were excluded
from the count comparison. The pipeline predicted 1,274 nuclei and 1,273
cells. Every predicted nucleus overlapped a predicted cell and one cell shared
two predicted nuclei. Of 43,875 relevant predicted cell-boundary pixels,
29,450 were within two pixels of the manual outline, giving a pooled directed
boundary fraction of 0.6712 and a mean field fraction of 0.6669. Per-field
fractions ranged from 0.5387 to 0.7453. The count difference was +192 nuclei.

The boundary measure is directed from predicted adjacent-cell boundaries to
the union of manual outlines. It can reward an incomplete segmentation and
does not establish object correspondence. This trial also starts from raw
images, whereas the 64% result reported with BBBC007 used supplied nuclear
seeds and foreground. Twelve source TIFFs contained colored registration
crosses; the preparation retained exact scalar pixels where RGB channels
agreed and replaced the colored strokes with black. Original archive members
and both transformations remain hash-bound in the corpus manifest.

The original prediction manifest contains 96 entries and has SHA-256 digest
`9567656274363230aa11e7786a9c414c690394468997d93de19e67fea8d33493`.
The scorer used a path-qualified projection over the same files, with SHA-256
digest `379e103d80a2ca3155a5809114974f8e55b6c710bea74f0686552627f20a7289`.
The typed score receipt has SHA-256 digest
`54cff8a050163cfe990b6a747973bce4303dae2022c060f82093a2bf22b87f74`.

## BBBC013 protein-translocation assay

BBBC013 contains FKHR-GFP and DRAQ nuclear images from a 96-well dose-response
experiment with Wortmannin and LY294002. Four wells spanning the low and high
response ranges were available during development; the remaining 92 wells were
held out. The agent identified nuclei, expanded matched cell regions, subtracted
the retained nuclei to define cytoplasm and measured GFP intensity in the
matched nuclear and cytoplasmic objects. The frozen endpoint was the per-well
mean of cell-level mean nuclear GFP divided by mean cytoplasmic GFP.

The held-out run retained 1,472 artifacts and 92 endpoint tables. The scorer
required every table to contain identical nonempty nuclear and cytoplasmic
object-label domains and rejected zero cytoplasmic denominators. It evaluated
14,262 matched cells, ranging from 97 to 270 cells per held-out well. The four
positive and four negative control wells for each treatment gave a Z-prime of
0.751 for Wortmannin and 0.554 for LY294002. Mean nuclear-to-cytoplasmic GFP was
7.235 versus 0.915 for the Wortmannin controls and 7.219 versus 1.127 for the
LY294002 controls. The independently disclosed dose series increased across
the expected concentration range for both treatments.

The reference supplies treatment, dose and control identities rather than
manual segmentation truth. The result therefore establishes recovery of the
assay response under the frozen analysis, not nucleus or cell-boundary accuracy.
Wells, rather than individual cells, are the independent control replicates.

The development prediction manifest has SHA-256 digest
`70b9c3e7546a5149430448ceecd367cfa1843f6e15e7146102417fffdeb5a75f`.
The held-out prediction manifest contains 1,472 entries and has SHA-256 digest
`62e86100ce3f99a7261b309184854d2a3d04139302900c7578d34a50cd8dfc6d`.
The held-out typed score receipt has SHA-256 digest
`d18ef5636ce3b55965e80771db815063f3d4f212507dddd3e47c22f49c976504`.

## Operational findings

The trials also exercised the same persistence and viewer surfaces available
to an ordinary MCP client. BBBC039 initially exposed that automatic labels and
terminal measurement artifacts were previewed in memory despite requested disk
materialization. The repair assigned label, ROI and measurement persistence to
their artifact declarations and propagated the compiled result root through
the existing path planner. Re-execution retained all expected native outputs
without changing the frozen scientific functions or parameters.

The BBBC039 held-out run also showed that a shared absolute result directory
can overwrite equal basenames from two plate partitions. The overwrite was
preserved in the receipt; development outputs were reconstructed later in a
partition-specific directory using the frozen pipeline. BBBC007 visual review
exposed an inherited offscreen Qt platform in a detached viewer. A
declaration-owned launch policy now replaces known noninteractive Qt plugins
with the host interactive plugin while preserving explicitly selected custom
platforms. A separate replay produced byte-identical label TIFFs and
measurement CSVs before native screenshots were accepted.

BBBC013 exposed two declaration-boundary failures before its development
pipeline was frozen. Edge filtering relabeled a Boolean mask and could merge
touching cells; it now relabels the retained integer object labels. A
replacement-primary operation has two object-label outputs, so its owning
module now identifies which output carries the secondary-object threshold
measurements. Materialized mixed-subject measurement tables also now retain
their declared object subject and source-image identity. Regression tests and
the four development wells verified matched nuclei, cells and cytoplasm before
the held-out path was disclosed.

These corrections concern persistence, namespace, presentation and declared
object identity. They did not tune the blind segmentation parameters or use
held-out reference values during authoring.
