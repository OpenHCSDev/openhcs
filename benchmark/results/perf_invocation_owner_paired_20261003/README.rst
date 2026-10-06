Fresh invocation-owner paired checkpoint
========================================

Source ``c59eaa55fe3d3e49f3ecb727a14a91e56e2957f6`` contains the six
carrier removals and checkpoint correction. It precedes the output-record
binding specialization merged as PR #544. Both ordinary repetitions and two
fresh measured native repetitions are retained in ``timing_summary.json``.

3D mean OpenHCS execution is 9.021577s, total 11.020390s, and native warm
invocation 14.793260s: 1.63976x execution and 1.34235x total. Speckles means
are 1.554196s execution, 2.433450s total and 1.964025s native: 1.26369x
execution and 0.807095x total. The two 3D execution observations are 9.616797s
and 8.426356s; Speckles observations are 1.810366s and 1.298026s. This
spread and two observations do not establish causal improvement or regression.

All eight cross-comparisons pass the existing strict scientific image,
measurement, nonempty-domain, correlation and complete-inventory gates. Native
CP 3.9/JVM 11 import, loading and full warmup are outside its invocation clock.
Mandatory OpenHCS READY preparation and server startup/shutdown are outside
pipeline clocks. OpenHCS execution excludes compilation; total includes it
and ordinary OUTCOMES completion. One well, one inline worker and one native
CPU thread are used, with the ordinary memory observer.

``qualification.json`` pins the original controller, source/dependency/input
joins, full strict-science report and verified lossless scientific custody
archive. The archive is 1,766,472 bytes for all 377 scientific files; its
SHA-256 is ``1cf533efca21da3638ae43931b5f5685a8790e3c45ae812622d10efcbcbfa6e8``.
Full strict report SHA-256 is
``08710272d7e7cbb14d6d12ab184532573267c777b68d86bfddd3d226a4270e3b``.
All original outputs remain retained. The local artifact paths are custody
references, not a claim that this directory is a standalone runnable bundle.

This is a current two-case descriptive checkpoint. Full30, scaling, fresh
scaling figures and the performance goal remain unfinished.
