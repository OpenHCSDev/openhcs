Receiving10: independent persisted-pixel check
==============================================

The complete public10 PipelineDocument declares2 SPAWN workers, two synthetic
12x15 uint16 input axes and registered worker_bootstrap_probe_708. Viewer
streaming is off. The task owner reports ordinary execution completion;
parent did not submit or replay any native operation.

Parent independently read the two original source TIFFs and two persisted
output TIFFs under the declared engineering HDD root:
/run/media/ts/hdd/openhcs-engineering/
engineering721725-public10-94-20261005.

Both A01 and A04 retain12x15 shape and uint16 dtype. All180 pixels on each
axis equal the corresponding source plus1:360/360 pixel comparisons pass.
This supports the original installed custom-callable task result, not just
source-test serialization or process startup.

The subsequent parent attempt to read outcomes01.json as UTF8 JSON failed:
the file begins with a compressed signature. This is an offline reader-format
mistake, not a native execution failure, and no operation was repeated.
The existing runtime-observation owner must decode its own export; Singer
retains that verification and original terminal/reobservation acceptance.
This receipt makes no independent observation-decoding, metadata/calibration,
closure or biological claim. It covers these exact two synthetic pixel arrays.
