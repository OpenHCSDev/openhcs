# D2: the whole Cellpose surface, derived from Cellpose

Branch `feature/cellpose-full-surface`, stacked on `feature/cellpose-n2v2-custom-functions`
(draft PR #1230) with `origin/main` merged. Measured 2026-10-12 against the installed
Cellpose 3.1.1.3 (torch 2.14.1+cpu, NumPy 2.0.2, private venv) and shallow clones of the four
platforms. Owner direction: "there's no reason why we aren't exposing the same amount of
functions. remember there's no real limits."

## 1. What is wrong

OpenHCS before this job reaches 18 of 361 measured Cellpose parameters and capabilities: the
151-line example `examples/custom_functions/cellpose_segment.py` restates six of `eval`'s 24
parameters and three of 25 model names. Every parameter it restates is a copy of a fact
Cellpose owns (name, default, meaning), so it goes stale when Cellpose changes, and each
capability it lacks (restoration, size estimation, training, flows, 20 normalization and
tiling controls) needs another hand-written copy.

## 2. The surface, measured

Sources:

| What | Reference |
|---|---|
| Cellpose API | installed `cellpose==3.1.1.3`: `inspect.signature` of every entry point, `models.MODEL_NAMES`, `denoise.MODEL_NAMES`, `models.normalize_default` |
| Cellpose CLI | tag `v3.1.1.3` (`e6eec15`), `cellpose/cli.py` |
| CellProfiler | `CellProfiler-plugins` `5aaa4e5` (2026-09-30), `active_plugins/runcellpose.py` (settings revision 8) |
| BIOP (Fiji) | `ijl-utilities-wrappers` `812f582` (2025-12-17), `wrappers/cellpose/**` |
| napari | `cellpose-napari` `b2a2331` (2024-10-27), `_dock_widget.py` |
| QuPath | `qupath-extension-cellpose` `5d14816` (2026-07-06), `CellposeBuilder.java`, `Cellpose2D.java` |
| Cellpose 4.x | tag `v4.2.1.1` (`a54cb48`), read only, not installed |

Cell values: `y` a dedicated typed control; `f` reachable only by typing a CLI flag into a
free-text field (BIOP `additional_flags`, QuPath `addParameter`); `s` supplied by the platform
instead of a control (the note says from where); `-` absent. The table is rendered by a script
from Cellpose's own signatures, so the API column cannot omit a parameter.

Cellpose 3.1.1.3; 361 rows.

| Column | dedicated control (y) | free CLI flag only (f) | supplied by the platform (s) | absent (-) |
|---|---|---|---|---|
| API | 342 | 0 | 0 | 19 |
| CLI | 190 | 0 | 0 | 171 |
| CellProfiler | 63 | 0 | 0 | 298 |
| BIOP | 35 | 153 | 0 | 173 |
| napari | 43 | 0 | 0 | 318 |
| QuPath | 66 | 134 | 0 | 161 |
| OpenHCS before | 18 | 0 | 0 | 343 |
| OpenHCS after | 279 | 0 | 74 | 8 |

Rows where the OpenHCS-after column is `-`:

- `anisotropy taken from the image's voxel spacing` (platform feature around Cellpose): GAP: a function is not told the voxel size; needs a runtime-bound physical-pixel-size parameter
- `GPU memory share per worker` (platform feature around Cellpose): GAP: `torch.cuda.set_per_process_memory_fraction` is process state, owned by device assignment (DL1)
- `run in a Docker/Podman container or foreign conda environment` (platform feature around Cellpose): GAP: OpenHCS calls the library in its own interpreter; needs an out-of-process function runner
- `diameter from drawn shapes` (platform feature around Cellpose): GAP: interactive viewer tool; the result is a number the user types into `diameter`
- `tile a large image, run, merge objects across tile borders` (platform feature around Cellpose): GAP for whole-slide images only: needs a tile-and-merge-labels step; Cellpose's own tiling (`bsize`, `tile_overlap`, `augment`) is exposed
- `simplify object contours` (platform feature around Cellpose): GAP: polygon objects are QuPath's representation; OpenHCS ROIs are traced from labels unsimplified
- `classify / annotate created objects` (platform feature around Cellpose): GAP: object classes are a QuPath data-model concept with no OpenHCS artifact kind
- `Omnipose` (platform feature around Cellpose): GAP: a different library (omnipose); it gets its own declaration with the same mechanism

| Group | Parameter or capability | Cellpose default | API | CLI | CellProfiler | BIOP | napari | QuPath | OpenHCS before | OpenHCS after | Note |
|---|---|---|---|---|---|---|---|---|---|---|---|
| CellposeModel() | `gpu` | False | y | y | y | f | - | y | - | y |  |
| CellposeModel() | `pretrained_model` | False | y | y | y | y | y | y | - | y |  |
| CellposeModel() | `model_type` | None | y | y | y | y | y | y | y | y |  |
| CellposeModel() | `mkldnn` | True | y | y | - | f | - | f | - | y |  |
| CellposeModel() | `diam_mean` | 30.0 | y | y | - | f | - | f | - | y |  |
| CellposeModel() | `device` | None | y | y | - | f | - | f | - | s | the platform assigns devices (DL1); until then Cellpose's own `gpu` flag chooses |
| CellposeModel() | `nchan` | 2 | y | y | - | f | - | f | - | y |  |
| CellposeModel() | `pretrained_model_ortho` | None | y | y | - | f | - | f | - | y |  |
| CellposeModel() | `backbone` | 'default' | y | y | - | f | - | f | - | y |  |
| CellposeModel.eval | `x` |  | y | y | y | y | y | y | y | s | the step's image stack |
| CellposeModel.eval | `batch_size` | 8 | y | y | - | f | - | f | - | y |  |
| CellposeModel.eval | `resample` | True | y | y | - | f | y | f | - | y |  |
| CellposeModel.eval | `channels` | None | y | y | y | y | y | y | y | y |  |
| CellposeModel.eval | `channel_axis` | None | y | y | - | f | y | f | - | y |  |
| CellposeModel.eval | `z_axis` | None | y | y | - | f | - | f | - | y |  |
| CellposeModel.eval | `normalize` | True | y | y | - | f | - | y | - | y |  |
| CellposeModel.eval | `invert` | False | y | y | y | f | - | f | - | y |  |
| CellposeModel.eval | `rescale` | None | y | - | - | - | - | - | - | y |  |
| CellposeModel.eval | `diameter` | None | y | y | y | y | y | y | y | y |  |
| CellposeModel.eval | `flow_threshold` | 0.4 | y | y | y | f | y | y | y | y |  |
| CellposeModel.eval | `cellprob_threshold` | 0.0 | y | y | y | f | y | y | y | y |  |
| CellposeModel.eval | `do_3D` | False | y | y | y | f | y | f | y | y |  |
| CellposeModel.eval | `anisotropy` | None | y | y | y | f | - | f | - | y |  |
| CellposeModel.eval | `flow3D_smooth` | 0 | y | y | - | f | - | f | - | y |  |
| CellposeModel.eval | `stitch_threshold` | 0.0 | y | y | y | f | y | f | - | y |  |
| CellposeModel.eval | `min_size` | 15 | y | y | y | f | - | f | - | y |  |
| CellposeModel.eval | `max_size_fraction` | 0.4 | y | - | - | - | - | - | - | y |  |
| CellposeModel.eval | `niter` | None | y | y | - | f | - | f | - | y |  |
| CellposeModel.eval | `augment` | False | y | y | - | f | - | f | - | y |  |
| CellposeModel.eval | `tile_overlap` | 0.1 | y | - | - | - | - | - | - | y |  |
| CellposeModel.eval | `bsize` | 224 | y | - | - | - | - | - | - | y |  |
| CellposeModel.eval | `interp` | True | y | y | - | f | - | f | - | y |  |
| CellposeModel.eval | `compute_masks` | True | y | - | - | - | - | - | - | y |  |
| CellposeModel.eval | `progress` | None | y | - | - | - | - | - | - | s | a Qt progress bar of Cellpose's own GUI; no meaning outside it |
| normalize options | `lowhigh` | None | y | - | - | - | - | - | - | y | field of the derived options dataclass |
| normalize options | `percentile` | None | y | y | - | f | - | f | - | y | field of the derived options dataclass |
| normalize options | `normalize` | True | y | y | - | f | - | y | - | y | field of the derived options dataclass |
| normalize options | `norm3D` | True | y | - | - | - | - | - | - | y | field of the derived options dataclass |
| normalize options | `sharpen_radius` | 0 | y | - | - | - | - | - | - | y | field of the derived options dataclass |
| normalize options | `smooth_radius` | 0 | y | - | - | - | - | - | - | y | field of the derived options dataclass |
| normalize options | `tile_norm_blocksize` | 0 | y | - | - | - | - | - | - | y | field of the derived options dataclass |
| normalize options | `tile_norm_smooth3D` | 1 | y | - | - | - | - | - | - | y | field of the derived options dataclass |
| normalize options | `invert` | False | y | y | - | f | - | f | - | y | field of the derived options dataclass |
| Cellpose() | `gpu` | False | y | y | y | f | - | f | - | y |  |
| Cellpose() | `model_type` | 'cyto3' | y | y | y | f | y | f | - | y |  |
| Cellpose() | `nchan` | 2 | y | - | - | - | - | - | - | y |  |
| Cellpose() | `device` | None | y | y | - | f | - | f | - | s | the platform assigns devices (DL1); until then Cellpose's own `gpu` flag chooses |
| Cellpose() | `backbone` | 'default' | y | - | - | - | - | - | - | y |  |
| Cellpose.eval | `x` |  | y | y | y | f | - | f | - | s | the step's image stack |
| Cellpose.eval | `batch_size` | 8 | y | y | - | f | - | f | - | y |  |
| Cellpose.eval | `channels` | [0, 0] | y | y | y | f | - | f | - | y |  |
| Cellpose.eval | `channel_axis` | None | y | y | - | f | - | f | - | y |  |
| Cellpose.eval | `invert` | False | y | y | y | f | - | f | - | y |  |
| Cellpose.eval | `normalize` | True | y | y | - | f | - | f | - | y |  |
| Cellpose.eval | `diameter` | 30.0 | y | y | y | f | - | f | - | y |  |
| Cellpose.eval | `do_3D` | False | y | y | y | f | - | f | - | y |  |
| SizeModel() | `cp_model` |  | y | y | - | f | - | f | - | s | built from the model parameters of the same function |
| SizeModel() | `device` | None | y | y | - | f | - | f | - | s | the platform assigns devices (DL1); until then Cellpose's own `gpu` flag chooses |
| SizeModel() | `pretrained_size` | None | y | - | - | - | - | - | - | y |  |
| SizeModel.eval | `x` |  | y | y | - | f | y | f | - | s | the step's image stack |
| SizeModel.eval | `channels` | None | y | y | - | f | y | f | - | y |  |
| SizeModel.eval | `channel_axis` | None | y | y | - | f | y | f | - | y |  |
| SizeModel.eval | `normalize` | True | y | y | - | f | - | f | - | y |  |
| SizeModel.eval | `invert` | False | y | y | - | f | - | f | - | y |  |
| SizeModel.eval | `augment` | False | y | - | - | - | - | - | - | y |  |
| SizeModel.eval | `batch_size` | 8 | y | y | - | f | - | f | - | y |  |
| SizeModel.eval | `progress` | None | y | - | - | - | - | - | - | s | a Qt progress bar of Cellpose's own GUI; no meaning outside it |
| DenoiseModel() | `gpu` | False | y | - | y | - | - | - | - | y |  |
| DenoiseModel() | `pretrained_model` | False | y | - | - | - | - | - | - | y |  |
| DenoiseModel() | `nchan` | 1 | y | - | - | - | - | - | - | y |  |
| DenoiseModel() | `model_type` | None | y | - | y | - | - | - | - | y |  |
| DenoiseModel() | `chan2` | False | y | - | y | - | - | - | - | y |  |
| DenoiseModel() | `diam_mean` | 30.0 | y | - | - | - | - | - | - | y |  |
| DenoiseModel() | `device` | None | y | - | - | - | - | - | - | s | the platform assigns devices (DL1); until then Cellpose's own `gpu` flag chooses |
| DenoiseModel.eval | `x` |  | y | - | y | - | - | - | - | s | the step's image stack |
| DenoiseModel.eval | `batch_size` | 8 | y | - | - | - | - | - | - | y |  |
| DenoiseModel.eval | `channels` | None | y | - | y | - | - | - | - | y |  |
| DenoiseModel.eval | `channel_axis` | None | y | - | - | - | - | - | - | y |  |
| DenoiseModel.eval | `z_axis` | None | y | - | - | - | - | - | - | y |  |
| DenoiseModel.eval | `normalize` | True | y | - | - | - | - | - | - | y |  |
| DenoiseModel.eval | `rescale` | None | y | - | - | - | - | - | - | y |  |
| DenoiseModel.eval | `diameter` | None | y | - | y | - | - | - | - | y |  |
| DenoiseModel.eval | `tile` | True | y | - | - | - | - | - | - | y |  |
| DenoiseModel.eval | `do_3D` | False | y | - | - | - | - | - | - | y |  |
| DenoiseModel.eval | `tile_overlap` | 0.1 | y | - | - | - | - | - | - | y |  |
| DenoiseModel.eval | `bsize` | 224 | y | - | - | - | - | - | - | y |  |
| CellposeDenoiseModel() | `gpu` | False | y | y | - | f | - | f | - | y |  |
| CellposeDenoiseModel() | `pretrained_model` | False | y | y | - | f | - | f | - | y |  |
| CellposeDenoiseModel() | `model_type` | None | y | y | - | f | - | f | - | y |  |
| CellposeDenoiseModel() | `restore_type` | 'denoise_cyto3' | y | y | - | f | - | f | - | y |  |
| CellposeDenoiseModel() | `nchan` | 2 | y | - | - | - | - | - | - | y |  |
| CellposeDenoiseModel() | `chan2_restore` | False | y | y | - | f | - | f | - | y |  |
| CellposeDenoiseModel() | `device` | None | y | y | - | f | - | f | - | s | the platform assigns devices (DL1); until then Cellpose's own `gpu` flag chooses |
| CellposeDenoiseModel.eval | `x` |  | y | y | - | f | - | f | - | s | the step's image stack |
| CellposeDenoiseModel.eval | `batch_size` | 8 | y | y | - | f | - | f | - | y |  |
| CellposeDenoiseModel.eval | `channels` | None | y | y | - | f | - | f | - | y |  |
| CellposeDenoiseModel.eval | `channel_axis` | None | y | y | - | f | - | f | - | y |  |
| CellposeDenoiseModel.eval | `z_axis` | None | y | y | - | f | - | f | - | y |  |
| CellposeDenoiseModel.eval | `normalize` | True | y | y | - | f | - | f | - | y |  |
| CellposeDenoiseModel.eval | `rescale` | None | y | - | - | - | - | - | - | y |  |
| CellposeDenoiseModel.eval | `diameter` | None | y | y | - | f | - | f | - | y |  |
| CellposeDenoiseModel.eval | `tile_overlap` | 0.1 | y | - | - | - | - | - | - | y |  |
| CellposeDenoiseModel.eval | `augment` | False | y | y | - | f | - | f | - | y |  |
| CellposeDenoiseModel.eval | `resample` | True | y | y | - | f | - | f | - | y |  |
| CellposeDenoiseModel.eval | `invert` | False | y | y | - | f | - | f | - | y |  |
| CellposeDenoiseModel.eval | `flow_threshold` | 0.4 | y | y | - | f | - | f | - | y |  |
| CellposeDenoiseModel.eval | `cellprob_threshold` | 0.0 | y | y | - | f | - | f | - | y |  |
| CellposeDenoiseModel.eval | `do_3D` | False | y | y | - | f | - | f | - | y |  |
| CellposeDenoiseModel.eval | `anisotropy` | None | y | y | - | f | - | f | - | y |  |
| CellposeDenoiseModel.eval | `stitch_threshold` | 0.0 | y | y | - | f | - | f | - | y |  |
| CellposeDenoiseModel.eval | `min_size` | 15 | y | y | - | f | - | f | - | y |  |
| CellposeDenoiseModel.eval | `niter` | None | y | y | - | f | - | f | - | y |  |
| CellposeDenoiseModel.eval | `interp` | True | y | y | - | f | - | f | - | y |  |
| CellposeDenoiseModel.eval | `bsize` | 224 | y | - | - | - | - | - | - | y |  |
| CellposeDenoiseModel.eval | `flow3D_smooth` | 0 | y | y | - | f | - | f | - | y |  |
| train.train_seg | `net` |  | y | y | - | f | - | y | - | s | built from the model parameters of the same function |
| train.train_seg | `train_data` | None | y | - | - | - | - | - | - | s | the step's image stack |
| train.train_seg | `train_labels` | None | y | - | - | - | - | - | - | s | a label artifact of an earlier step |
| train.train_seg | `train_files` | None | y | y | - | f | - | y | - | s | file-list transport of train_data; OpenHCS reads the plate through its storage backends |
| train.train_seg | `train_labels_files` | None | y | y | - | f | - | y | - | s | as train_files |
| train.train_seg | `train_probs` | None | y | y | - | f | - | f | - | y |  |
| train.train_seg | `test_data` | None | y | - | - | - | - | - | - | s | a second image input |
| train.train_seg | `test_labels` | None | y | - | - | - | - | - | - | s | a second label artifact |
| train.train_seg | `test_files` | None | y | y | - | f | - | y | - | s | as train_files |
| train.train_seg | `test_labels_files` | None | y | y | - | f | - | y | - | s | as train_files |
| train.train_seg | `test_probs` | None | y | y | - | f | - | f | - | y |  |
| train.train_seg | `load_files` | True | y | y | - | f | - | f | - | s | only meaningful with file lists |
| train.train_seg | `batch_size` | 8 | y | y | - | f | - | y | - | y |  |
| train.train_seg | `learning_rate` | 0.005 | y | y | - | f | - | y | - | y |  |
| train.train_seg | `n_epochs` | 2000 | y | y | - | f | - | y | - | y |  |
| train.train_seg | `weight_decay` | 1e-05 | y | y | - | f | - | f | - | y |  |
| train.train_seg | `momentum` | 0.9 | y | - | - | - | - | - | - | y |  |
| train.train_seg | `SGD` | False | y | y | - | f | - | f | - | y |  |
| train.train_seg | `channels` | None | y | y | - | f | - | f | - | y |  |
| train.train_seg | `channel_axis` | None | y | y | - | f | - | f | - | y |  |
| train.train_seg | `rgb` | False | y | - | - | - | - | - | - | y |  |
| train.train_seg | `normalize` | True | y | y | - | f | - | f | - | y |  |
| train.train_seg | `compute_flows` | False | y | - | - | - | - | - | - | y |  |
| train.train_seg | `save_path` | None | y | y | - | f | - | y | - | s | a declared output directory |
| train.train_seg | `save_every` | 100 | y | y | - | f | - | f | - | y |  |
| train.train_seg | `save_each` | False | y | - | - | - | - | - | - | y |  |
| train.train_seg | `nimg_per_epoch` | None | y | y | - | f | - | f | - | y |  |
| train.train_seg | `nimg_test_per_epoch` | None | y | y | - | f | - | f | - | y |  |
| train.train_seg | `rescale` | True | y | - | - | - | - | - | - | y |  |
| train.train_seg | `scale_range` | None | y | - | - | - | - | - | - | y |  |
| train.train_seg | `bsize` | 224 | y | - | - | - | - | - | - | y |  |
| train.train_seg | `min_train_masks` | 5 | y | y | - | f | - | y | - | y |  |
| train.train_seg | `model_name` | None | y | y | - | f | - | y | - | y |  |
| train.train_size | `net` |  | y | y | - | f | - | f | - | s | built from the model parameters of the same function |
| train.train_size | `pretrained_model` |  | y | y | - | f | - | f | - | y |  |
| train.train_size | `train_data` | None | y | - | - | - | - | - | - | s | the step's image stack |
| train.train_size | `train_labels` | None | y | - | - | - | - | - | - | s | a label artifact of an earlier step |
| train.train_size | `train_files` | None | y | y | - | f | - | f | - | s | file-list transport of train_data; OpenHCS reads the plate through its storage backends |
| train.train_size | `train_labels_files` | None | y | y | - | f | - | f | - | s | as train_files |
| train.train_size | `train_probs` | None | y | y | - | f | - | f | - | y |  |
| train.train_size | `test_data` | None | y | - | - | - | - | - | - | s | a second image input |
| train.train_size | `test_labels` | None | y | - | - | - | - | - | - | s | a second label artifact |
| train.train_size | `test_files` | None | y | y | - | f | - | f | - | s | as train_files |
| train.train_size | `test_labels_files` | None | y | y | - | f | - | f | - | s | as train_files |
| train.train_size | `test_probs` | None | y | y | - | f | - | f | - | y |  |
| train.train_size | `load_files` | True | y | y | - | f | - | f | - | s | only meaningful with file lists |
| train.train_size | `min_train_masks` | 5 | y | y | - | f | - | f | - | y |  |
| train.train_size | `channels` | None | y | y | - | f | - | f | - | y |  |
| train.train_size | `channel_axis` | None | y | y | - | f | - | f | - | y |  |
| train.train_size | `rgb` | False | y | - | - | - | - | - | - | y |  |
| train.train_size | `normalize` | True | y | y | - | f | - | f | - | y |  |
| train.train_size | `nimg_per_epoch` | None | y | y | - | f | - | f | - | y |  |
| train.train_size | `nimg_test_per_epoch` | None | y | y | - | f | - | f | - | y |  |
| train.train_size | `batch_size` | 64 | y | y | - | f | - | f | - | y |  |
| train.train_size | `scale_range` | 1.0 | y | - | - | - | - | - | - | y |  |
| train.train_size | `bsize` | 512 | y | - | - | - | - | - | - | y |  |
| train.train_size | `l2_regularization` | 1.0 | y | - | - | - | - | - | - | y |  |
| train.train_size | `n_epochs` | 10 | y | - | - | - | - | - | - | y |  |
| denoise.train | `net` |  | y | - | - | - | - | - | - | s | built from the model parameters of the same function |
| denoise.train | `train_data` | None | y | - | - | - | - | - | - | s | the step's image stack |
| denoise.train | `train_labels` | None | y | - | - | - | - | - | - | s | a label artifact of an earlier step |
| denoise.train | `train_files` | None | y | - | - | - | - | - | - | s | file-list transport of train_data; OpenHCS reads the plate through its storage backends |
| denoise.train | `test_data` | None | y | - | - | - | - | - | - | s | a second image input |
| denoise.train | `test_labels` | None | y | - | - | - | - | - | - | s | a second label artifact |
| denoise.train | `test_files` | None | y | - | - | - | - | - | - | s | as train_files |
| denoise.train | `train_probs` | None | y | - | - | - | - | - | - | y |  |
| denoise.train | `test_probs` | None | y | - | - | - | - | - | - | y |  |
| denoise.train | `lam` | [1.0, 1.5, 0.0] | y | - | - | - | - | - | - | y |  |
| denoise.train | `scale_range` | 0.5 | y | - | - | - | - | - | - | y |  |
| denoise.train | `seg_model_type` | 'cyto2' | y | - | - | - | - | - | - | y |  |
| denoise.train | `save_path` | None | y | - | - | - | - | - | - | s | a declared output directory |
| denoise.train | `save_every` | 100 | y | - | - | - | - | - | - | y |  |
| denoise.train | `save_each` | False | y | - | - | - | - | - | - | y |  |
| denoise.train | `poisson` | 0.7 | y | - | - | - | - | - | - | y |  |
| denoise.train | `beta` | 0.7 | y | - | - | - | - | - | - | y |  |
| denoise.train | `blur` | 0.7 | y | - | - | - | - | - | - | y |  |
| denoise.train | `gblur` | 1.0 | y | - | - | - | - | - | - | y |  |
| denoise.train | `iso` | True | y | - | - | - | - | - | - | y |  |
| denoise.train | `uniform_blur` | False | y | - | - | - | - | - | - | y |  |
| denoise.train | `downsample` | 0.0 | y | - | - | - | - | - | - | y |  |
| denoise.train | `ds_max` | 7 | y | - | - | - | - | - | - | y |  |
| denoise.train | `learning_rate` | 0.005 | y | - | - | - | - | - | - | y |  |
| denoise.train | `n_epochs` | 500 | y | - | - | - | - | - | - | y |  |
| denoise.train | `weight_decay` | 1e-05 | y | - | - | - | - | - | - | y |  |
| denoise.train | `batch_size` | 8 | y | - | - | - | - | - | - | y |  |
| denoise.train | `nimg_per_epoch` | None | y | - | - | - | - | - | - | y |  |
| denoise.train | `nimg_test_per_epoch` | None | y | - | - | - | - | - | - | y |  |
| denoise.train | `model_name` | None | y | - | - | - | - | - | - | y |  |
| dynamics.compute_masks | `dP` |  | y | - | - | - | - | - | - | s | the flow artifact |
| dynamics.compute_masks | `cellprob` |  | y | - | - | - | - | - | - | s | the cell-probability artifact |
| dynamics.compute_masks | `p` | None | y | - | - | - | - | - | - | y |  |
| dynamics.compute_masks | `niter` | 200 | y | - | - | - | - | - | - | y |  |
| dynamics.compute_masks | `cellprob_threshold` | 0.0 | y | - | - | - | - | - | - | y |  |
| dynamics.compute_masks | `flow_threshold` | 0.4 | y | - | - | - | - | - | - | y |  |
| dynamics.compute_masks | `interp` | True | y | - | - | - | - | - | - | y |  |
| dynamics.compute_masks | `do_3D` | False | y | - | - | - | - | - | - | y |  |
| dynamics.compute_masks | `min_size` | -1 | y | - | - | - | - | - | - | y |  |
| dynamics.compute_masks | `max_size_fraction` | 0.4 | y | - | - | - | - | - | - | y |  |
| dynamics.compute_masks | `device` | device(type='cpu') | y | - | - | - | - | - | - | s | the platform assigns devices (DL1); until then Cellpose's own `gpu` flag chooses |
| dynamics.resize_and_compute_masks | `dP` |  | y | - | - | - | y | - | - | s | the flow artifact |
| dynamics.resize_and_compute_masks | `cellprob` |  | y | - | - | - | y | - | - | s | the cell-probability artifact |
| dynamics.resize_and_compute_masks | `niter` | 200 | y | - | - | - | - | - | - | y |  |
| dynamics.resize_and_compute_masks | `cellprob_threshold` | 0.0 | y | - | - | - | y | - | - | y |  |
| dynamics.resize_and_compute_masks | `flow_threshold` | 0.4 | y | - | - | - | y | - | - | y |  |
| dynamics.resize_and_compute_masks | `interp` | True | y | - | - | - | - | - | - | y |  |
| dynamics.resize_and_compute_masks | `do_3D` | False | y | - | - | - | - | - | - | y |  |
| dynamics.resize_and_compute_masks | `min_size` | 15 | y | - | - | - | - | - | - | y |  |
| dynamics.resize_and_compute_masks | `max_size_fraction` | 0.4 | y | - | - | - | - | - | - | y |  |
| dynamics.resize_and_compute_masks | `resize` | None | y | - | - | - | - | - | - | y |  |
| dynamics.resize_and_compute_masks | `device` | device(type='cpu') | y | - | - | - | - | - | - | s | the platform assigns devices (DL1); until then Cellpose's own `gpu` flag chooses |
| dynamics.masks_to_flows | `masks` |  | y | - | - | - | - | - | - | s | a label artifact of an earlier step |
| dynamics.masks_to_flows | `device` | device(type='cpu') | y | - | - | - | - | - | - | s | the platform assigns devices (DL1); until then Cellpose's own `gpu` flag chooses |
| dynamics.masks_to_flows | `niter` | None | y | - | - | - | - | - | - | y |  |
| dynamics.remove_bad_flow_masks | `masks` |  | y | - | - | - | - | - | - | s | a label artifact of an earlier step |
| dynamics.remove_bad_flow_masks | `flows` |  | y | - | - | - | - | - | - | y |  |
| dynamics.remove_bad_flow_masks | `threshold` | 0.4 | y | - | - | - | - | - | - | y |  |
| dynamics.remove_bad_flow_masks | `device` | device(type='cpu') | y | - | - | - | - | - | - | s | the platform assigns devices (DL1); until then Cellpose's own `gpu` flag chooses |
| utils.masks_to_outlines | `masks` |  | y | - | - | - | y | - | - | s | a label artifact of an earlier step |
| utils.masks_to_edges | `masks` |  | y | - | - | - | - | - | - | s | a label artifact of an earlier step |
| utils.masks_to_edges | `threshold` | 1.0 | y | - | - | - | - | - | - | y |  |
| utils.remove_edge_masks | `masks` |  | y | - | - | - | - | - | - | s | a label artifact of an earlier step |
| utils.remove_edge_masks | `change_index` | True | y | - | - | - | - | - | - | y |  |
| utils.dilate_masks | `masks` |  | y | - | - | - | - | - | - | s | a label artifact of an earlier step |
| utils.dilate_masks | `n_iter` | 5 | y | - | - | - | - | - | - | y |  |
| utils.stitch3D | `masks` |  | y | - | - | - | - | - | - | s | a label artifact of an earlier step |
| utils.stitch3D | `stitch_threshold` | 0.25 | y | - | - | - | - | - | - | y |  |
| utils.fill_holes_and_remove_small_masks | `masks` |  | y | - | - | - | - | - | - | s | a label artifact of an earlier step |
| utils.fill_holes_and_remove_small_masks | `min_size` | 15 | y | - | - | - | - | - | - | y |  |
| utils.diameters | `masks` |  | y | - | - | - | - | - | - | s | a label artifact of an earlier step |
| utils.distance_to_boundary | `masks` |  | y | - | - | - | - | - | - | s | a label artifact of an earlier step |
| utils.get_mask_compactness | `masks` |  | y | - | - | - | - | - | - | s | a label artifact of an earlier step |
| utils.get_mask_perimeters | `masks` |  | y | - | - | - | - | - | - | s | a label artifact of an earlier step |
| utils.size_distribution | `masks` |  | y | - | - | - | - | - | - | s | a label artifact of an earlier step |
| metrics.average_precision | `masks_true` |  | y | - | - | - | - | - | - | s | a label artifact |
| metrics.average_precision | `masks_pred` |  | y | - | - | - | - | - | - | s | a label artifact |
| metrics.average_precision | `threshold` | [0.5, 0.75, 0.9] | y | - | - | - | - | - | - | y |  |
| metrics.aggregated_jaccard_index | `masks_true` |  | y | - | - | - | - | - | - | s | a label artifact |
| metrics.aggregated_jaccard_index | `masks_pred` |  | y | - | - | - | - | - | - | s | a label artifact |
| metrics.boundary_scores | `masks_true` |  | y | - | - | - | - | - | - | s | a label artifact |
| metrics.boundary_scores | `masks_pred` |  | y | - | - | - | - | - | - | s | a label artifact |
| metrics.boundary_scores | `scales` |  | y | - | - | - | - | - | - | y |  |
| metrics.mask_ious | `masks_true` |  | y | - | - | - | - | - | - | s | a label artifact |
| metrics.mask_ious | `masks_pred` |  | y | - | - | - | - | - | - | s | a label artifact |
| metrics.flow_error | `maski` |  | y | - | - | - | - | - | - | s | a label artifact |
| metrics.flow_error | `dP_net` |  | y | - | - | - | - | - | - | s | the flow artifact |
| metrics.flow_error | `device` | None | y | - | - | - | - | - | - | s | the platform assigns devices (DL1); until then Cellpose's own `gpu` flag chooses |
| pretrained segmentation model | `cyto3` |  | y | y | y | y | y | y | y | y |  |
| pretrained segmentation model | `nuclei` |  | y | y | y | y | y | y | y | y |  |
| pretrained segmentation model | `cyto2_cp3` |  | y | y | y | y | y | y | - | y |  |
| pretrained segmentation model | `tissuenet_cp3` |  | y | y | y | y | y | y | - | y |  |
| pretrained segmentation model | `livecell_cp3` |  | y | y | y | y | y | y | - | y |  |
| pretrained segmentation model | `yeast_PhC_cp3` |  | y | y | y | y | y | y | - | y |  |
| pretrained segmentation model | `yeast_BF_cp3` |  | y | y | y | y | y | y | - | y |  |
| pretrained segmentation model | `bact_phase_cp3` |  | y | y | y | y | y | y | - | y |  |
| pretrained segmentation model | `bact_fluor_cp3` |  | y | y | y | y | y | y | - | y |  |
| pretrained segmentation model | `deepbacs_cp3` |  | y | y | y | y | y | y | - | y |  |
| pretrained segmentation model | `cyto2` |  | y | y | y | y | y | y | y | y |  |
| pretrained segmentation model | `cyto` |  | y | y | y | y | y | y | - | y |  |
| pretrained segmentation model | `CPx` |  | y | y | - | y | - | y | - | y |  |
| pretrained segmentation model | `transformer_cp3` |  | y | y | - | y | - | y | - | y |  |
| pretrained segmentation model | `neurips_cellpose_default` |  | y | y | - | y | - | y | - | y |  |
| pretrained segmentation model | `neurips_cellpose_transformer` |  | y | y | - | y | - | y | - | y |  |
| pretrained segmentation model | `neurips_grayscale_cyto2` |  | y | y | - | y | - | y | - | y |  |
| pretrained segmentation model | `CP` |  | y | y | - | y | - | y | - | y |  |
| pretrained segmentation model | `TN1` |  | y | y | - | y | - | y | - | y |  |
| pretrained segmentation model | `TN2` |  | y | y | - | y | - | y | - | y |  |
| pretrained segmentation model | `TN3` |  | y | y | - | y | - | y | - | y |  |
| pretrained segmentation model | `LC1` |  | y | y | - | y | - | y | - | y |  |
| pretrained segmentation model | `LC2` |  | y | y | - | y | - | y | - | y |  |
| pretrained segmentation model | `LC3` |  | y | y | - | y | - | y | - | y |  |
| pretrained segmentation model | `LC4` |  | y | y | - | y | - | y | - | y |  |
| pretrained restoration model | `denoise_cyto3` |  | y | y | y | f | - | f | - | y |  |
| pretrained restoration model | `deblur_cyto3` |  | y | y | y | f | - | f | - | y |  |
| pretrained restoration model | `upsample_cyto3` |  | y | y | y | f | - | f | - | y |  |
| pretrained restoration model | `oneclick_cyto3` |  | y | y | - | f | - | f | - | y |  |
| pretrained restoration model | `denoise_cyto2` |  | y | y | - | f | - | f | - | y |  |
| pretrained restoration model | `denoise_per_cyto2` |  | y | y | - | f | - | f | - | y |  |
| pretrained restoration model | `denoise_seg_cyto2` |  | y | y | - | f | - | f | - | y |  |
| pretrained restoration model | `denoise_rec_cyto2` |  | y | y | - | f | - | f | - | y |  |
| pretrained restoration model | `deblur_cyto2` |  | y | y | - | f | - | f | - | y |  |
| pretrained restoration model | `deblur_per_cyto2` |  | y | y | - | f | - | f | - | y |  |
| pretrained restoration model | `deblur_seg_cyto2` |  | y | y | - | f | - | f | - | y |  |
| pretrained restoration model | `deblur_rec_cyto2` |  | y | y | - | f | - | f | - | y |  |
| pretrained restoration model | `upsample_cyto2` |  | y | y | - | f | - | f | - | y |  |
| pretrained restoration model | `upsample_per_cyto2` |  | y | y | - | f | - | f | - | y |  |
| pretrained restoration model | `upsample_seg_cyto2` |  | y | y | - | f | - | f | - | y |  |
| pretrained restoration model | `upsample_rec_cyto2` |  | y | y | - | f | - | f | - | y |  |
| pretrained restoration model | `oneclick_cyto2` |  | y | y | - | f | - | f | - | y |  |
| pretrained restoration model | `oneclick_per_cyto2` |  | y | y | - | f | - | f | - | y |  |
| pretrained restoration model | `oneclick_seg_cyto2` |  | y | y | - | f | - | f | - | y |  |
| pretrained restoration model | `oneclick_rec_cyto2` |  | y | y | - | f | - | f | - | y |  |
| pretrained restoration model | `aniso_cyto2` |  | y | y | - | f | - | f | - | y |  |
| pretrained restoration model | `denoise_nuclei` |  | y | y | y | f | - | f | - | y |  |
| pretrained restoration model | `denoise_per_nuclei` |  | y | y | - | f | - | f | - | y |  |
| pretrained restoration model | `denoise_seg_nuclei` |  | y | y | - | f | - | f | - | y |  |
| pretrained restoration model | `denoise_rec_nuclei` |  | y | y | - | f | - | f | - | y |  |
| pretrained restoration model | `deblur_nuclei` |  | y | y | y | f | - | f | - | y |  |
| pretrained restoration model | `deblur_per_nuclei` |  | y | y | - | f | - | f | - | y |  |
| pretrained restoration model | `deblur_seg_nuclei` |  | y | y | - | f | - | f | - | y |  |
| pretrained restoration model | `deblur_rec_nuclei` |  | y | y | - | f | - | f | - | y |  |
| pretrained restoration model | `upsample_nuclei` |  | y | y | y | f | - | f | - | y |  |
| pretrained restoration model | `upsample_per_nuclei` |  | y | y | - | f | - | f | - | y |  |
| pretrained restoration model | `upsample_seg_nuclei` |  | y | y | - | f | - | f | - | y |  |
| pretrained restoration model | `upsample_rec_nuclei` |  | y | y | - | f | - | f | - | y |  |
| pretrained restoration model | `oneclick_nuclei` |  | y | y | - | f | - | f | - | y |  |
| pretrained restoration model | `oneclick_per_nuclei` |  | y | y | - | f | - | f | - | y |  |
| pretrained restoration model | `oneclick_seg_nuclei` |  | y | y | - | f | - | f | - | y |  |
| pretrained restoration model | `oneclick_rec_nuclei` |  | y | y | - | f | - | f | - | y |  |
| pretrained restoration model | `aniso_nuclei` |  | y | y | - | f | - | f | - | y |  |
| output | `label masks, per plane (2D)` |  | y | y | y | y | y | y | y | y |  |
| output | `label masks, 3D volume (do_3D)` |  | y | y | y | f | y | - | y | y | QuPath's extension is 2D only |
| output | `label masks, 2D stitched across Z` |  | y | y | y | f | y | - | - | y |  |
| output | `flows as RGB image` |  | y | y | - | f | y | f | - | y |  |
| output | `flow field dP` |  | y | y | - | - | - | - | - | y | CLI: inside _seg.npy |
| output | `cell-probability map` |  | y | y | y | - | y | - | - | y |  |
| output | `style vector per image` |  | y | - | - | - | - | - | - | y |  |
| output | `estimated diameter per image` |  | y | y | y | - | y | - | - | y | CellProfiler shows it in the display only |
| output | `restored image` |  | y | y | - | f | - | f | - | y | CellProfiler displays it but its save setting is not wired (runcellpose.py:1044-1050) |
| output | `outlines image` |  | y | y | y | f | y | f | - | y |  |
| output | `ROI archive of the masks` |  | y | y | - | f | - | y | y | y |  |
| output | `object count per image` |  | - | - | y | - | - | y | y | y |  |
| output | `trained model file` |  | y | y | - | - | - | y | - | y |  |
| output | `training and test loss per epoch` |  | y | y | - | - | - | y | - | y |  |
| output | `trained size-model file` |  | y | y | - | - | - | f | - | y |  |
| platform feature around Cellpose | `second (nuclear) image chosen as a separate input` |  | - | - | y | y | y | y | y | y | group the step by channel; `channel_axis=0` |
| platform feature around Cellpose | `clip input to 1st-99th percentile before Cellpose` |  | - | - | y | - | - | y | - | y | an earlier step (`percentile_normalize`), or Cellpose's own `percentile` option |
| platform feature around Cellpose | `remove masks touching the image edge` |  | y | y | y | f | - | y | - | y | `utils.remove_edge_masks` as a derived function |
| platform feature around Cellpose | `anisotropy taken from the image's voxel spacing` |  | - | - | y | - | - | - | - | - | GAP: a function is not told the voxel size; needs a runtime-bound physical-pixel-size parameter |
| platform feature around Cellpose | `GPU memory share per worker` |  | - | - | y | - | - | - | - | - | GAP: `torch.cuda.set_per_process_memory_fraction` is process state, owned by device assignment (DL1) |
| platform feature around Cellpose | `GPU test button` |  | - | - | y | - | - | - | - | y | preparation runs the model before readiness |
| platform feature around Cellpose | `run in a Docker/Podman container or foreign conda environment` |  | - | - | y | y | - | y | - | - | GAP: OpenHCS calls the library in its own interpreter; needs an out-of-process function runner |
| platform feature around Cellpose | `keep the model loaded between images` |  | y | - | y | - | y | - | y | y | one model per (constructor arguments) per worker process |
| platform feature around Cellpose | `diameter from drawn shapes` |  | - | - | - | - | y | - | - | - | GAP: interactive viewer tool; the result is a number the user types into `diameter` |
| platform feature around Cellpose | `recompute masks from stored flows with new thresholds` |  | y | - | - | - | y | - | - | y | `dynamics.resize_and_compute_masks` fed by the flow and probability artifacts |
| platform feature around Cellpose | `downsample to a requested pixel size before Cellpose` |  | - | - | - | - | - | y | - | y | an earlier rescale step; Cellpose's `rescale`/`diameter` |
| platform feature around Cellpose | `tile a large image, run, merge objects across tile borders` |  | - | - | - | - | - | y | - | - | GAP for whole-slide images only: needs a tile-and-merge-labels step; Cellpose's own tiling (`bsize`, `tile_overlap`, `augment`) is exposed |
| platform feature around Cellpose | `expand nuclei to cells` |  | - | - | - | - | - | y | - | y | `utils.dilate_masks`; scikit-image `expand_labels` |
| platform feature around Cellpose | `shape and intensity measurements of the objects` |  | - | - | y | - | - | y | y | y | `measure_labelled_objects`, scikit-image `regionprops` steps on the label artifact |
| platform feature around Cellpose | `simplify object contours` |  | - | - | - | - | - | y | - | - | GAP: polygon objects are QuPath's representation; OpenHCS ROIs are traced from labels unsimplified |
| platform feature around Cellpose | `classify / annotate created objects` |  | - | - | - | - | - | y | - | - | GAP: object classes are a QuPath data-model concept with no OpenHCS artifact kind |
| platform feature around Cellpose | `export training pairs from annotated regions` |  | - | - | - | - | - | y | - | y | training reads images and a label artifact from the plate; no export step is needed |
| platform feature around Cellpose | `quality metrics of a trained model on held-out images` |  | y | - | - | - | - | y | - | y | `metrics.average_precision`, `aggregated_jaccard_index`, `boundary_scores` as derived functions |
| platform feature around Cellpose | `training loss graph` |  | - | - | - | - | - | y | - | y | loss table as a measurement output |
| platform feature around Cellpose | `per-well result tables with plate metadata` |  | - | - | y | - | - | - | y | y |  |
| platform feature around Cellpose | `Omnipose` |  | - | - | y | y | - | y | - | - | GAP: a different library (omnipose); it gets its own declaration with the same mechanism |
| platform feature around Cellpose | `Cellpose-SAM (4.x)` |  | - | - | y | y | - | y | - | y | the derivation reads the installed version; section 4 lists what 4.x changes |

Findings from the survey that bear on the design:

- **Cellpose has no type annotations.** Types exist only in its docstrings
  (`name (type, optional): text`) and defaults. `CellposeModel.__init__` documents 7 of 9
  parameters; `SizeModel` and `CellposeDenoiseModel` document none of their `eval` parameters.
- **The `normalize` documentation is stale against the code.** `eval`'s docstring lists the keys
  `sharpen`, `tile_norm`; the code reads `models.normalize_default`, whose keys are `lowhigh,
  percentile, normalize, norm3D, sharpen_radius, smooth_radius, tile_norm_blocksize,
  tile_norm_smooth3D, invert`. The dict in the code is the owner.
- **`eval(normalize=<bool>)` mutates `models.normalize_default` in place** (`models.py:493-500`:
  `normalize_params = normalize_default` then item assignment). A call with `normalize=False`
  changes the default every later dict-style call starts from, in that process. Passing the
  complete nine-key dict on every call is independent of that state; the derived function does so.
- `models.MODEL_NAMES` lists `CPx` twice; 25 distinct names.
- CellProfiler never exposes flows, tiling, normalization options, batch size or training, and
  its "save preprocessed image" setting is not wired to an output. The mature plugin is narrower
  than Cellpose's API by 279 rows.
- BIOP and QuPath expose few typed controls (35 and 66) and reach the rest of the CLI through a
  free-text field: untyped, undocumented in the tool, unchecked until the subprocess fails.

## 3. Cellpose 4.x (Cellpose-SAM) against 3.1.1.3

| Item | 3.1.1.3 | 4.2.1.1 | Effect on a derived surface |
|---|---|---|---|
| `CellposeModel()` | `gpu, pretrained_model=False, model_type, mkldnn, diam_mean=30, device, nchan=2, pretrained_model_ortho, backbone` | `gpu, pretrained_model="cpsam_v2", model_type, diam_mean=None, device, nchan=None, use_bfloat16=True` | `mkldnn`, `pretrained_model_ortho`, `backbone` disappear; `use_bfloat16` appears; no OpenHCS edit |
| `model_type`, `diam_mean`, `nchan` | used | accepted, warned, ignored | still shown (Cellpose still declares them) |
| `eval` | 24 parameters | no `invert`, no `interp`; `bsize=None` (256 for cpsam) | two controls disappear, one default changes |
| `eval(channels=)` | selects channels | warned, ignored; 3-channel input, `channel_axis` | shown but inert |
| `eval(diameter=)` | `None` means the model's training diameter | `None`/0 means no rescale, else `30/diameter` | same control, Cellpose's new meaning |
| `eval(flow3D_smooth=)` | number | number or ZYX triple | the stated type must widen (checked by the guard) |
| `models.Cellpose`, `SizeModel`, `train.train_size` | exist | removed | the size-estimation functions are not derived |
| `denoise.DenoiseModel`, `CellposeDenoiseModel`, 38 restoration models | exist | removed | the restoration functions are not derived |
| `train.train_seg` | `momentum`, `channels`, `rgb`; lr 0.005, 2000 epochs, batch 8, wd 1e-5, `rescale=True`, `bsize=224` | adds `class_weights`; lr 1e-5, 100 epochs, batch 1, wd 0.1, `rescale=False`, `bsize=None`; `SGD` ignored | controls and defaults follow |
| Model names | 25 | `cpsam_v2`, `cpdino`, `cpdino-vitb`, `cpsam` | the derived enum follows `MODEL_NAMES` |
| Weights | 26.6 MB each, cellpose.org | 1.2 GB, Hugging Face | preparation cost only |
| CLI | `--chan`, `--chan2`, `--invert`, `--restore_type`, `--diam_mean`, `--train_size`, `--transformer` functional | accepted and ignored; adds `--train_batch_size`, `--bsize`, `--save_each` | not used by OpenHCS |

3.1.1.3 stays the recommended line (D1 section 5: runs on CPU, fits an 8 GB card, has the
nuclear, size and restoration models).

## 4. Decision: (a), derive from Cellpose

**A registry that derives each function from Cellpose's own callables at the installed
version.** Reason, from the measurements: 342 API rows against 18 exposed is the cost of
restating; a guard test over a restated list (option b) would report each Cellpose change and
still need a person to copy it in, while the derivation needs no edit (section 3, last column).
The one owner of a parameter's name, default, order and description is Cellpose (P1: a required
relation is declared once, in the mechanism that derives it; a restated list is a copy).
OpenHCS states only what Cellpose cannot.

### The general rule (any library whose API is "construct a model, call it")

*One catalogue function per library call. Each argument of that call that is a model object,
`self` included, is a resource built by its constructor; the constructor's parameters join the
function's signature. The image argument and the resources are supplied; every other parameter
of the call and of the constructors becomes a control with the library's name, default, order
and description.*

| Library call | Resources | Catalogue function |
|---|---|---|
| `models.CellposeModel.eval` | `self` = `CellposeModel(...)` | `cellpose:segment` |
| `models.Cellpose.eval` | `self` = `Cellpose(...)` | `cellpose:segment_estimating_diameter` |
| `models.SizeModel.eval` | `self` = `SizeModel(cp_model=CellposeModel(...), ...)` (nested) | `cellpose:estimate_diameter` |
| `denoise.DenoiseModel.eval` | `self` = `DenoiseModel(...)` | `cellpose:restore` |
| `denoise.CellposeDenoiseModel.eval` | `self` = `CellposeDenoiseModel(...)` | `cellpose:restore_and_segment` |
| `train.train_seg` | `net` = `CellposeModel(...).net`, not shared | `cellpose:train_segmentation` |
| `train.train_size` | `net` = `SizeModel(...)` | `cellpose:train_size` |
| `denoise.train` | `net` = `DenoiseModel(...).net` | `cellpose:train_restoration` |
| `dynamics.resize_and_compute_masks`, `utils.*`, `metrics.*` | none | `cellpose:<module>.<name>` |

The same table for the next library is its whole declaration: StarDist
(`StarDist2D.predict_instances`, `self` = `StarDist2D.from_pretrained(name)`), Omnipose (the same
shape as Cellpose 1.x), a plain torch model (`Module.__call__`, `self` = a loader function taking
a declared weights file).

### What OpenHCS states, because Cellpose cannot

A parameter gets its annotation from, in order: (1) Cellpose's annotation (none today);
(2) Cellpose's documented type for that name, anywhere in the library's docstrings
(`int`, `float`, `bool`, `str`; `None` default makes it `Optional`); (3) the type of the default;
(4) a statement in the OpenHCS declaration. A parameter none of these types is a derivation
error naming the parameter: nothing is typed `Any`, and a new Cellpose parameter with a
documented scalar type appears with no edit. Statements are a small family (ABC with behaviour
on the subclasses, not a kind enum):

| Statement | Meaning | Cellpose uses |
|---|---|---|
| `ImageStack` | this parameter receives the step's stack | `x`, `train_data` |
| `Supplied(reason)` | no control; stays at the library default or is filled by the function | `progress`, `device` |
| `Stated(annotation, to_library)` | OpenHCS states the type and how the typed value becomes the library's | below |
| `Resource(factory, attribute, shared)` | built from the factory's own derived parameters | `self`, `net`, `cp_model` |

Stated types for Cellpose (each is checked against the installed signature by a test that fails
when the name is gone, so a statement cannot outlive its parameter):

- `model_type`: an enum derived from `models.MODEL_NAMES` (restoration: `denoise.MODEL_NAMES`),
  created at import with its module and qualified name set so generated pipeline code imports it.
- `pretrained_model`, `pretrained_size`, `pretrained_model_ortho`: `Optional[PlateInputFile]`
  (a custom or trained model is a declared file; `Path` to `str`).
- `normalize`: a frozen dataclass derived from `models.normalize_default` (one field per key,
  default from the dict, type from the value; `lowhigh` and `percentile`, whose defaults are
  `None`, are stated `Optional[tuple[float, float]]`), converted to the full dict. Field
  descriptions come from `transforms.normalize_img`'s docstring, the function that consumes them.
- `channels`: `tuple[int, int]` to `list`.
- training: `save_path` `PlateOutputDirectory`; `train_probs`, `test_probs`
  `Optional[tuple[float, ...]]`; `lam` `tuple[float, float, float]`.

**Array contract.** Cellpose's `eval` documents NumPy in and NumPy out and copies tensors to
host itself (D1 section 2), so the functions are declared NumPy; that is the truth of the
library, not a fallback. A stack `(N, Y, X)` is a list of N planes unless the user names the
axis with Cellpose's own `z_axis=0` (a volume: `do_3D` or `stitch_threshold`) or `channel_axis=0`
(one multi-channel image). No OpenHCS parameter is added for this. Not expressible: a volume with
a second channel needs `(Z, C, Y, X)`; a step's stack is three-dimensional (platform change:
a step grouped by two components that receives a 4D stack).

**The model as a resource.** One model per (factory, constructor arguments) per process, built
on first use and during preparation; training resources are built fresh (`shared=False`).
`device` is supplied. Until `refactor/DL1-device-and-memory-types` lands, Cellpose's own `gpu`
control chooses (it is Cellpose's parameter, shown as Cellpose documents it); after DL1 the
declaration becomes NumPy in and out with torch execution and `gpu`/`device` are both supplied.

**Outputs** (existing declarations only):

| Cellpose result | Declared as |
|---|---|
| masks (per plane, volume, stitched) | `ObjectLabelsArtifactType`, ROI archive + label TIFF |
| cell probability `(N, Y, X)` | `ImageArtifactType` |
| flow field dP `(N, Y, X, 2 or 3)` | `ImageArtifactType` (channels last) |
| flows as RGB `(N, Y, X, 3)` | `ImageArtifactType` |
| styles `(N, 256)`, diameter, object count per image | `MeasurementsArtifactType` rows (derived row dataclass) |
| restored image | the function's main image output |
| trained model | file under the declared `PlateOutputDirectory` |
| train and test loss per epoch | `MeasurementsArtifactType` rows |

`segment` returns its input image unchanged as the main output, so a later step still sees
pixels; `restore` returns the restored image.

### Where things live

- `openhcs/processing/backends/lib_registry/model_library.py`: the generic derivation
  (statements, docstring type reader, signature and docstring synthesis, resource cache). No
  Cellpose name in it.
- `openhcs/processing/backends/lib_registry/cellpose_registry.py`: `CellposeRegistry`
  (auto-registered; available when `importlib.util.find_spec("cellpose")`; imports Cellpose
  only when the catalogue asks for its functions) and the Cellpose declaration (the table above).
- `openhcs/processing/backends/lib_registry/derived/cellpose.py`: the importable home of the
  derived functions, enums and dataclasses (workers and the cache resolve a function by module
  and name; generated code imports the enum and dataclass from here). Derivation runs at import
  and is deterministic.
- `pyproject.toml`: optional extra `cellpose = ["cellpose>=3.1.1.3,<4"]`.
- `examples/custom_functions/cellpose_segment.py` stays as it is: the manuscript's demonstration
  that a user can add a tool in one file. The catalogue surface is the maintained one.

Platform corrections this needs (found, not worked around):

1. `OpenHCSRegistry.get_module_patterns()` returns `["openhcs"]`, so it claims any decorated
   function under `openhcs.*`, although it only catalogues `openhcs.processing.backends.*`
   outside `lib_registry` (`openhcs_registry.py:613-634, 740-742, 926-956`). Its claim must equal
   its inventory, or a derived function is claimed as `openhcs:<name>` in a process without a
   loaded catalogue.
2. The registry cache tracks only `unified_registry.py` and the registry's own file
   (`unified_registry.py:814-825`); the generic derivation module joins `cache_source_mtimes`.
3. `tests/unit/test_library_registry_discovery.py:892` asserts the CPU-only registry set equals
   `{"openhcs", "skimage"}`. Cellpose needs torch, so `CellposeRegistry.supports_cpu_only()` is
   false and the assertion holds; the registry file must not import Cellpose at module level
   (`:887`).

## 5. Dependencies on work in progress (code against main; a test marked expected-to-fail for each)

| Need | Branch | Today on main | Expected-to-fail test |
|---|---|---|---|
| A trained model consumed by segmentation in the same pipeline; one training call per plate | `refactor/DL2-declared-files-between-steps` | compile: `Declared input file does not exist` (`vfs_protocol.py:149-159`); training is called once per well | train then segment in one pipeline |
| Device assigned by the platform, CPU when there is no GPU | `refactor/DL1-device-and-memory-types`, arraybridge 0.5.0 | a torch-executing declaration fails to compile without CUDA (`framework_device_resolver.py:56-60`) | NumPy in/out with torch execution compiles on CPU and `gpu` is no longer a control |
| Weights downloaded and model warmed for the step's own parameters before readiness | `refactor/DL4-custom-function-preparation` | the hook takes no arguments: only the default model can be prepared | preparing a non-default model before readiness |
| Output records the model name, weights hash and Cellpose version | `refactor/DL3-output-provenance` | no provenance in `openhcs_metadata.json` | metadata names the model |

## 6. Guards and tests

- Every parameter of every declared Cellpose callable is a control, a supplied parameter with a
  reason, or a resource; none is `Any`; every statement names a parameter that exists.
- Derived defaults equal Cellpose's; the model enum equals `MODEL_NAMES`; the options dataclass
  equals `normalize_default`.
- Each function equals the direct Cellpose call with the same arguments (bit-identical, CPU).
- 3D on a synthetic stack; restore then segment; train (few epochs) then segment with the
  trained file as far as main allows.
- Each capability through the execution server in a pipeline.
- All skip with "Cellpose is an optional dependency" when it is not installed.

## 7. New-case experiment

Adding StarDist must be one declaration table and no change to `model_library.py`. Recorded
when run.

## Progress

Done: sections 1 to 7 (measurement, matrix, design); draft PR #1234. Nothing is built yet.
Scratch (untracked, in the worktree): `.claude/venv` (CPU venv with Cellpose 3.1.1.3; delete at
the end), `.claude/scripts/matrix.py` (renders section 2), `.claude/scripts/probe_eval.py`
(return shapes), `.claude/platform-clones/` (delete at the end).

### Facts the implementation must respect (measured on this branch)

Platform:

- Registry classes in `lib_registry/` are discovered by importing every module of that package
  (not recursively). The registry file must not import Cellpose or torch at module level
  (`tests/unit/test_library_registry_discovery.py:887`); use `importlib.util.find_spec` in
  `is_library_available`. A registry that raises or returns false is skipped with a warning
  (`registry_service.py:241-272`). A registry whose cache cannot round-trip breaks the whole
  catalogue (`registry_service.py:162-166`).
- A plain `LibraryRegistryBase` subclass needs `get_library_version`, `is_library_available`,
  `discover_functions`, `get_library_object`, class attributes `_registry_name`,
  `MODULES_TO_SCAN`, `MEMORY_TYPE`, `FLOAT_DTYPE`, a zero-argument `__init__`, and either
  `_generate_function_name` or an override of `metadata_for_declared_callable`
  (`unified_registry.py:337-362`). `get_module_patterns` must cover the module that holds the
  derived functions (`owns_module`).
- A function is transported as a reference and resolved in every process by
  `import_module(metadata.module)` + `getattr(original_name)`; `inspect.unwrap(metadata.func)`
  must be that object; the cache reloads the same way and re-applies
  `reconstruct_cached_callable` (`registry_service.py:441-530`, `unified_registry.py:688-782`).
  The module attribute is the memory-decorated function before the registry wrapper; keep one
  registry wrapper per declaration (precedent `openhcs_registry.py:243-261, 958-969`).
- Memory decorators can be applied to a closure with a synthesized `__signature__`,
  `__annotations__`, `__name__`, `__module__`, `__doc__` (checked):
  `numpy(func, contract=Pure3DContract, prepare=...)`; `artifact_outputs(...)` likewise.
  `Pure3DContract` is one call on the whole stack (`processing_contracts.py:1140`).
- Parameter descriptions come from `inspect.getdoc`, parsed as `Args:` with `name: text`
  lines; Cellpose's `name (type, optional): text` form is not parsed, so the synthesized
  docstring is written as `name: text`. A continuation line containing a colon is misread
  (D1 row 1c): strip or reflow.
- Dynamic enums and `make_dataclass` types must have `__module__`/`__qualname__` that resolve by
  import (`pycodify/core.py:69-73`). Nested frozen-dataclass parameters work end to end
  (precedent `count_cells_simple.py:316-320`). MCP authoring coerces only enum keyword values
  (`callable_contract.py:1539-1551`): check whether a dataclass parameter can be set through
  MCP and report it if not.
- Avoid parameter names that are `PipelineConfig` fields (`runtime_config_parameter`,
  `core/config.py:1417-1438`).
- Image artifacts: `ImageArtifactType` output precedent `basic_processor_jax.py:40-65` (extra
  image outputs kept off the main flow with `sidecar_role`), input precedent
  `numpy_processor.py:413-415`. Accepted shapes are `(N, H, W)` or `(N, H, W, C)`
  (`function_runtime.py:1093-1097`). Measurements: `DataclassMeasurementColumnarRows(rows, Row)`
  with `ArtifactMeasurementSubjectRelation()`. Labels in: `ArtifactSpec.input(name,
  ObjectLabelsArtifactType, parameter_name=...)`.
- Declared files: `PlateInputFile`, `PlateOutputFile`, `PlateInputDirectory`,
  `PlateOutputDirectory` (`vfs_protocol.py:211-214`), resolved at compile to absolute paths;
  an input file must exist at compile.
- Preparation: every `metadata.func` gets its `__openhcs_prepare__` run before readiness
  (`registry_service.py:178-212`); one shared hook runs once per function unless it memoizes.
- Guard tests a new registry touches: `tests/unit/test_library_registry_discovery.py`
  (`:709-765`, `:819-892`, `:895-1001`), `test_processing_module_liveness.py:139-178`,
  `test_catalog_optional_libraries.py`, `test_registry_keys_unique.py`,
  `test_e1_enum_dispatch_guards.py`.
- Smallest pipeline-through-the-server test to model on:
  `tests/integration/test_count_cells_simple_dual_channel.py`; private server:
  `ZMQExecutionClient.with_private_server()`.

Cellpose (from `.claude/scripts/probe_eval.py`):

- `CellposeModel.eval` on a list of N planes returns `(list of N (Y,X) uint16, list of N
  [rgb (Y,X,3) uint8, dP (2,Y,X) float32, cellprob (Y,X) float32], list of N styles (256,))`.
  With `z_axis=0` and `stitch_threshold>0`: masks `(Z,Y,X)`, flows `[(Z,Y,X,3), (2,Z,Y,X),
  (Z,Y,X)]`, styles `(Z,256)`. With `do_3D`: dP `(3,Z,Y,X)`, styles `(n,256)` with n not Z.
  With `channel_axis=0`: one `(Y,X)` result. `compute_masks=False`: masks is an empty array.
- `Cellpose.eval` adds a fourth element, the diameters (list of floats). `SizeModel.eval`
  returns `(diameters, diameters_from_styles)`. `DenoiseModel.eval` returns a list of
  `(Y,X,1)` float32. `CellposeDenoiseModel.eval` returns `(masks, flows, styles, restored)`.
- `Cellpose`, `SizeModel`, `CellposeDenoiseModel` constructors have no parameter docs in
  `__init__`; class docstrings carry `Args:` for `Cellpose` and `DenoiseModel` only.
- Weights download to `~/.cellpose/models` (present: `nucleitorch_0`, its size model,
  `denoise_nuclei`).

### What remains, in order

1. `model_library.py` (generic), `cellpose_registry.py`, `derived/cellpose.py`, the
   `OpenHCSRegistry` claim correction, `cache_source_mtimes`, the `cellpose` extra.
   Functions: `segment`, `segment_estimating_diameter`, `estimate_diameter`, `restore`,
   `restore_and_segment`; then `train_segmentation`, `train_size`, `train_restoration`; then the
   module functions (`dynamics.resize_and_compute_masks`, `utils.*`, `metrics.*` listed in
   `.claude/scripts/matrix.py`).
2. Tests of section 6, including the four expected-to-fail tests of section 5.
3. Pipeline runs through the execution server on CPU with a few fields of
   `/home/ts/code/projects/openhcs/.claude/cellpose-demo/data` (copy, do not modify).
4. GPU run commands (the 8 GB GPU venv does not fit: `/home` has 9 GB free).
5. Gates: `verify_branch.sh d2 <worktree>`, `smoke_local.sh`, `guardrails_local.sh`.
6. Update the matrix's last column to what was built; record the StarDist experiment or say it
   was not run.
