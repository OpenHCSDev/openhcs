# Shared uint8 numerical conversion

The authentic TrackObjects Tile float32 output contains 27,043,632 values (108,174,528 bytes), shape `(21, 264, 1626, 3)`. Untimed reconstruction through the production ColorToGray, OverlayOutlines and Tile owners matched all 21 qualified native PNGs. SaveImages requests one uint8 conversion of this whole buffer; its finite-range scale decision is global.

One private CPU4 pair received the original numerical strategy at **533.414 ms** and a two-pass typed prototype at **121.197 ms** (412.218 ms lower). This excludes reconstruction, imports/kernel preparation, PNG encoding, and the enclosing SaveImages callable. The original observed SaveImages callable envelope was 461.382 ms. The pair is a local premise, not a pipeline gain; allocator order and instrumentation differ. No whole-pipeline timing is reported here.

The production implementation strengthens the existing nominal `ImagePayloadUint8Strategy`: singular float32/float64 leaves share the typed algorithm and preserve registry replacement. The old NumPy algorithm remains for unsupported floating precision, integer and complex domains. Original dtype multiplication, nearest-even rounding, finite-range/nonfinite policies and independent outputs are preserved. Public payload conversion already admits plain NumPy pixels; direct generic strategy calls retain their existing ndarray hooks.

Normal `CallablePreparation` of SaveImages now reaches the actual numerical owner through its production import. Image-file formats derive the same preparation operations. Exactly four flat float32/float64 × writable/readonly signatures existed before numerical work and none were added by scalar, empty, Fortran, permuted-strided, non-native-byteorder, readonly or authentic whole-Track receiving. All 21 production PNG pixels were exact. The 71 focused existing serialization, SaveImages and preparation controls passed.

See [receiving.json](receiving.json) for source/input hashes, exactness and private scope. Whole Track ordinary execution and strict native comparison are pending before promotion; startup warmup remains outside pipeline clocks.
