# Private CellProfiler-compatible font engine

This directory contains unmodified source from FreeType 2.6.1, downloaded from
https://download-mirror.savannah.gnu.org/releases/freetype/freetype-old/freetype-2.6.1.tar.bz2
(SHA-256 `2f6e9a7de3ae8e85bdd2fe237e27d868d3ba7a27495e65906455c27722dd1a17`).
Only the upstream include/source trees, module/build declarations, and licenses
are retained. Generated objects, tools, examples, and platform build systems
are excluded. The upstream `modules.cfg` and module `rules.mk` declarations
determine the extension's compiled sources; OpenHCS does not maintain a second
module roster. Optional external compression/font libraries are disabled by
the upstream portable configuration; bundled zlib remains available.

FreeType is distributed under the FreeType License (`docs/FTL.TXT`, also shipped
in `THIRD_PARTY_LICENSES/FreeType.txt`). This software is based in part on the
work of the FreeType Team. No FreeType source files are modified.

The OpenHCS bridge derives plaintext metrics/bitmap placement from Matplotlib
3.7.5's `src/ft2font.cpp` (Matplotlib license; shipped separately), retaining
the old anisotropic eightfold horizontal pre-hint grid. The private engine is
statically compiled into `_font_raster_native`, with hidden visibility on Unix
and no DLL exports on Windows. It neither replaces nor exports symbols into
the current Matplotlib font engine. Normal package installation builds it;
rendering never compiles or launches an external process.

The existing tracking renderer consumes this primitive for plain-text labels.
Mathtext continues through the current Matplotlib renderer. Font files remain
selected by Matplotlib's existing font manager; no rendered glyph assets are
packaged. Missing glyphs and unsupported raster modes raise explicit errors.
