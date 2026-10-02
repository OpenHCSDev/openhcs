# Canonical colocalization preparation (#491)

Public library preparation previously omitted the object correlation reduction and calculated threshold arrays directly from float64 reduction maxima. Canonical object execution instead converts image pixels to float32 and derives threshold arrays through `ObjectColocalizationThresholdStage`. The first BeginnerSegmentation timing consequently compiled three overloads after READY. That first timing is not evidence for a fully prepared performance improvement.

The existing callable preparation hooks now exercise their existing canonical request and metric owners. Image preparation uses the same float32 image metric path. Object preparation covers threshold metrics and Costes-only requests, so both canonical threshold-array types remain prepared. The callback no longer maintains a kernel list or a separate threshold formula. Numerical processing bodies and registry readiness policy are unchanged.

The small preparation images and labels are lawful synthetic inputs. They are not captured scientific inputs; the preparation callback does not publish their results. Object preparation uses the canonical leading-channel image-pair interface without source metadata, while the readiness test also checks the public typed channel interface. These interfaces produce the same canonical float32 kernel signatures.

## Validation

- Fresh private-cache original probe: base reduction ready; correlation, threshold and RWC attempted late compilation. Canonical argument tuples exactly matched the retained production `.nbi` indexes. Original source/shared indexes remained unchanged.
- New subprocess control: public preparation followed by global refusal of both `Dispatcher.compile` and `Cache.load_overload`, across IMAGE/OBJECT/BOTH scopes and threshold/Costes enabled and disabled. Exact fallback pixels and input nonmutation are checked, along with independent inverse-ramp correlation.
- Existing colocalization setting/metric controls remain required. No pipeline speedup or actual-input science claim follows from synthetic readiness controls.

Retained local originals: `/var/tmp/openhcs-colocalization-public-ready-signatures-v1-20261002` contains the diagnostic setup failure; `...-v2-20261002/observations.json` contains the original coverage RED. The global AST census is `/var/tmp/openhcs-colocalization-stage-callback-global-ast-v1-20261002.json` (1,623 Python modules). Failed initial test-fixture expectations and the full-home cache error remain in `/var/tmp/openhcs-491-focused-controls-v1-20261002.log` through `...-v4-20261002.log`.
