# Paired manuscript build acceptance

The existing `paper/build_paper.py build` consumer completed both manuscript and supplement DOCX/PDF outputs and promoted `run-20261008T005359-8a1e29ff` to current. A subsequent `status` reported `state: current` and an empty changed-input list. The original build manifest/log are retained here; generated bundles remain under the ordinary ignored paper build directory.

Build-only paper-build is pinned to papers main `0417d0f2c4d4e7b540f1ef45cfc35007858a34e4`, whose existing caption layout supports the full-width option used by latest main. The earlier pin failed with an unsupported constructor argument (issue #1103). Reinstall the declared build dependency when updating an existing environment: its package version remains 0.1.0 across these commits.

The built manuscript contains generated execution median 6.393, minimum 3.542, total median 4.066 and minimum 2.660, and the explicit first-use/projected baseline interpretation. The source Markdown retains declared benchmark spans; values come from the same qualified figure owner.
