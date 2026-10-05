Retinal candidate08: regional split/merge tradeoff
=================================================

Independent parent review of original author MCP PNGs, not reference scoring.
The author remains unguided; these observations are not sent to the author.

Evidence root
-------------

/run/media/ts/hdd/openhcs-science/next-r0010-fresh09-96-20261005/
R0010_FRESH09_96/screenshots/

Personally opened at native recorded size:

* c08-se-ring-outline/20261005T012631596861Z_napari_6017_OpenHCS_Napari_Visualization.png
* c08-se-ring-labels/20261005T012642977984Z_napari_6017_OpenHCS_Napari_Visualization.png
* c08-nw-outline/20261005T012653426684Z_napari_6017_OpenHCS_Napari_Visualization.png

The first is raw plus red outlines; the second isolates the result at the
same southeast viewport. They show one connected, concave support enclosing
the previously partitioned lobes. The northwest raw-plus-outline view appears
to give the bright vertically adjacent pair one continuous outer contour.
That is an apparent merge requiring the author's label/seed check, not a
confirmed object-identity count inferred from an outline alone.

Source rationale and actual limits
----------------------------------

Original TRIAL.rst records candidate07's northwest seed separation108.06px
and southeast internal seed separation87.09px. Candidate08 raises suppression
from80 to95px on the same unclosed foreground. The proposed distance interval
does not guarantee the maxima operator will preserve the brighter/weak pair:
the actual response landscape matters, not only centre-to-centre distance.
Do not claim this explanation proven until the source operator and actual
changed seeds are inspected. The current view supports a regional tradeoff.

Candidate06's earlier closing trial was rejected by the author because it
bridged genuine neighbours. It is not an accepted preprocessing recipe.

Graded disposition
------------------

Southeast false partition: visually improved in this viewport.
Northwest genuine-pair preservation: apparent regression, identity check due.
Isolated-body outlines: several nearby bodies still plausibly represented.
Global missed/false detection rate: unmeasured; these crops cannot establish it.
Boundary perfection is not required to retain useful detection progress.
Current counts are algorithmic outputs, not manual ground truth.

Retain the earlier candidate and failed closing trial. Do not replace the
best checkpoint based on one attractive crop, erase the local improvement,
or declare the complete run failed because this pair remains unresolved.
Transfer a conditional lesson only after the author finishes and confirms
the relevant foreground, marker and partition mechanism; then test a fresh
author without these coordinates or settings.
