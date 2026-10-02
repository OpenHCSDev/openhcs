Secondary source image metadata export (#444)
===========================================

Advanced segmentation declares five illumination calibration images as
borrowed inputs. They have no produced image records. The original CPA
projection therefore left nine source-information fields NULL for every
calibration role at both executed sites: 90 missing values.

The fix projects declared source occurrences through the existing workspace
owner, exact execution scope and already allocated image-set numbering.
Repeated physical files retain distinct logical site occurrences; unexecuted
sites cannot create rows. Recorded metadata conflicts still fail.
File-format subclasses supply header geometry and explicit TIFF frame-grid
selection through the existing revision cache. Loaded pixels and file headers
share the pixel-semantics owner's channel-axis validation.

Qualification
-------------

Base main: 58ee773b0. Production code: f2e1959ad.
220 tests passed, including merged singleton and source-inspection controls.
Two existing thumbnail cast warnings remain. The unchanged architecture
ratchet passed against main, without exemptions or detector changes.

A fresh public ordinary Advanced run used one inline worker/thread, CPU5,
default OUTCOMES and memory observation. Registry/kernel warmup and server
startup/shutdown are outside pipeline clocks. Compilation: 1.851722s;
execution: 9.850824s; pipeline total: 12.732532s. This is one observation,
not a measured optimization benefit or scaling qualification.

Against the retained fresh native CP output, the unchanged scientific export
comparison reports zero differences. All 90 previously missing source fields
are populated. Seventy values match literally, including every filename,
frame, series, dimension, scaling value and MD5 digest. The remaining twenty
PathName/URL strings refer to native CP staging versus the original files.
The raw string comparison remains RED and is not relabeled as a pass.
A separate physical identity gate verifies URL-to-path correspondence,
same inode, identical resolved source and the original pinned native input
inventory SHA256 for all ten role/image-set pairs. No fields were excluded,
outputs rewritten or path strings substituted.

Limits
------

This proves the reported Advanced source-only calibration failure; it does
not qualify all thirty pipelines or saved intermediate object-label masks.
Nondefault explicit image series/index selectors absent from SourcePixelRef
remain unsupported and fail explicitly. No performance improvement is claimed.

Retained evidence
-----------------

* ``/var/tmp/issue444-main58ee-integration-controls-20261002.log``
  SHA256: ``7145af2feb7ad335068c13bdcfe92999c2aeb39a3496fb53aef5c6b43e9ed7cc``

* ``/var/tmp/issue444-main58ee-original-r0-20261002.json``
  SHA256: ``7c11d7ef0c409e423288c545dd36a60a5a4d7d27dcc2cf23869f01cc84215f83``

* ``/var/tmp/openhcs-issue444-main-advanced-ordinary-f2e195-20261002/source-freeze.json``
  SHA256: ``51bc14fd65b18837a75253e117c82059f191a24151ab45627b5b20b67b35ee3c``

* ``/var/tmp/openhcs-issue444-main-advanced-ordinary-f2e195-20261002/observations.json``
  SHA256: ``ed69851f866f42e8875c3c1be86a802d23943b3471eb25ac26e6af284ca3ea8c``

* ``/var/tmp/issue444-main-advanced-native-production-metadata-f2e195-20261002.json``
  SHA256: ``c974d513337783245547e19bf2c5342f14ca4ac0f944510c9b98bcdd2fc9ffbb``

* ``/var/tmp/issue444-main-advanced-source-file-identity-f2e195-20261002.json``
  SHA256: ``5bf511916f6a873171ea8f56d3cc21c2a1b5e2466083d4a7c2b46d4c03fc4a15``

