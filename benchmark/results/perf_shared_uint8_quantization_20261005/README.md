# Shared uint8 numerical conversion

The authentic TrackObjects Tile float32 output contains 27,043,632 values (108,174,528 bytes), shape `(21, 264, 1626, 3)`. Untimed reconstruction through the production ColorToGray, OverlayOutlines and Tile owners matched all 21 qualified native PNGs. SaveImages requests one uint8 conversion of this whole buffer; its finite-range scale decision is global.

One private CPU4 pair received the original numerical strategy at **533.414 ms** and a two-pass typed prototype at **121.197 ms** (412.218 ms lower). This excludes reconstruction, imports/kernel preparation, PNG encoding, and the enclosing SaveImages callable. The original observed SaveImages callable envelope was 461.382 ms. The pair is a local premise, not a pipeline gain; allocator order and instrumentation differ. This private pair alone provides no whole-pipeline estimate; production qualification is reported separately below.

The production implementation strengthens the existing nominal `ImagePayloadUint8Strategy`: singular float32/float64 leaves share the typed algorithm and preserve registry replacement. The old NumPy algorithm remains for unsupported floating precision, integer and complex domains. Original dtype multiplication, nearest-even rounding, finite-range/nonfinite policies and independent outputs are preserved. Public payload conversion already admits plain NumPy pixels; direct generic strategy calls retain their existing ndarray hooks.

Normal `CallablePreparation` of SaveImages now reaches the actual numerical owner through its production import. Image-file formats derive the same preparation operations. Exactly four flat float32/float64 × writable/readonly signatures existed before numerical work and none were added by scalar, empty, Fortran, permuted-strided, non-native-byteorder, readonly or authentic whole-Track receiving. All 21 production PNG pixels were exact. The 71 focused existing serialization, SaveImages and preparation controls passed.

See [receiving.json](receiving.json) for source/input hashes, exactness and private scope. Whole Track ordinary execution and strict native comparison passed at measured head `3a961d1873411525611415b8075ffad19bc2aec3`; startup warmup remains outside pipeline clocks.

## Qualified production receiving

One original 21-frame TrackObjects ordinary run received compilation **0.2551 s**, execution **3.4342 s**, total **3.7828 s**, RSS **1812.85 MB**. Authenticated retained native first-module→post-run execution was **8.9132 s** and full pipeline time **9.0830 s**: **2.59545× execution** and **2.40114× total**. Server/JVM/catalog/kernel startup is excluded. This is one production observation against the authenticated retained native observation; the difference from earlier OpenHCS observations also includes intervening main changes and is not attributable solely to this patch.

Strict science passed all 21 exact PNGs, 65 object rows and 21 image rows on both sides, measurement relationships and complete nonvacuous inventory. Source, physical inputs, retained native outputs, helpers, eight dependencies and four native ABIs passed custody checks. The ordinary and science processes returned zero; owned processes and runtime lease were released. The post-receiving main merge changes documentation only, preserving the measured production implementation.

[qualified-receiving.json](qualified-receiving.json) preserves the measured head, physical input hashes, ordinary/native receipt hashes and strict-science SHA256 `56453e4be49f353bdd1799d575817174cf19d7890539014a6f74b66f3e3a77ba`. Prior setup REDs remain in the private receiving namespace; no failed result was overwritten.
