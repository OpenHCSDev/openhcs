Ordinary BaSiCPy dependency checkpoint
=====================================

Integration owner: parent; paired OpenHCS PR217 and BaSiCPy PR2.
Publication explicitly authorized by Tristan on 2026-09-30.

The project metadata owns ``openhcs-basicpy>=1.3.1,<1.4``. It supplies the
reviewed JAX fork, retaining the upstream ``basicpy`` Python API.
No copied algorithm, API alias, extra installation registry or source-path
requirement is introduced. ``requirements-basicpy.txt`` is removed (recoverable
in Git); ArrayBridge already has its ordinary project dependency. Linux,
Windows and Apple Silicon receive the fork automatically. Intel macOS retains
core installation without modern JAX, whose CPU wheels exclude that platform.

Do not merge an unavailable dependency. The fork's merged packaging checkpoint
is ``8ca3be674d2e11602c152e5080ee4cdf94a780a3``; release automation is triggered
by ``v1.3.0``. That queued job was cancelled before any steps ran after an
installed-entrypoint check found a legacy TODO-only CLI. Issue313 and the
corrective fork checkpoint remove the dead CLI in place and advance to1.3.1;
the original tag/history are preserved. Registry availability and actual resolution must be verified
separately; neither a tag nor a wheel build is publication.

Actual validation
-----------------

Eight source contracts passed in 0.038s, including the ordinary dependency
specifier, platform markers, upstream parameter ownership and dtype declaration.
The fork wheel was installed into an owned target, without dependencies,
downloads or shared environment mutation. Both Python 3.12 and 3.14 import
that exact installed target as ``basicpy``, with metadata identifying
``openhcs-basicpy`` 1.3.0. Six real numerical/profile tests passed on each:
13.24s and 12.18s, respectively.

Four paired OpenHCS tests passed against that installed fork wheel in 10.36s:
the real decorated 2D/volume fits, stationary-biology negative control and
persisted acquisition fixture. The OpenHCS wheel itself builds successfully
and its METADATA declares the ordinary fork requirement, with no Git URLs.

The shared deterministic numerical control is now written as 24 independent
ImageXpress SITE files through the existing typed filename and image-format
owners. A real acquisition parser proves the calibration, SITE/channel/Z
values and exact input pixels. Existing fit assertions use the same numerical
generator, rather than a second scientific fixture recipe. Overwrite refusal
preserves every existing input file. These are synthetic controls, not blind
benchmark inputs or answers.

This receipt is not installed user-entrypoint, compiled/MCP, CUDA or biological
acceptance. The frozen blind run and shared installed runtime are unchanged.
Durable wheel/XML receipts are under
``/home/ts/wt/openhcs-issue-batch-20260929/basicpy-project-dependency-20260930``.
Owned disposable targets and bounded generated test files are under
``/home/ts/.cache/agent-scratch/basicpy-package-20260930``.
