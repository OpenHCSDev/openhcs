/* CellProfiler-compatible plaintext rasterization.
 * Adapted from Matplotlib 3.7.5 ft2font.cpp (Matplotlib license): set_size,
 * set_text, draw_glyphs_to_bitmap, FT2Image::draw_bitmap.
 * See THIRD_PARTY_LICENSES/Matplotlib.txt and vendor/freetype-2.6.1/README.md. */
#include <ft2build.h>
#include FT_FREETYPE_H
#include FT_GLYPH_H
#include <stdint.h>
#include <stdlib.h>
#include <limits.h>

int openhcs_render_text(const char *fontpath, double ptsize, double dpi,
                const uint32_t *text, size_t n, unsigned char **pixels, long *facts) {
    FT_Library library = NULL;
    FT_Face face = NULL;
    FT_Glyph *glyphs = calloc(n ? n : 1, sizeof(FT_Glyph));
    int error = 0;
    *pixels = NULL;
    if (!glyphs) return 10002;
    error = FT_Init_FreeType(&library);
    if (error) goto done;
    error = FT_New_Face(library, fontpath, 0, &face);
    if (error) goto done;
    error = FT_Set_Char_Size(face, (FT_F26Dot6)(ptsize * 64), 0,
                            (FT_UInt)(dpi * 8), (FT_UInt)dpi);
    if (error) goto done;
    FT_Matrix transform = {65536 / 8, 0, 0, 65536};
    FT_Set_Transform(face, &transform, NULL);
    FT_Vector pen = {0, 0};
    FT_BBox bbox = {32000, 32000, -32000, -32000};
    FT_UInt previous = 0;
    for (size_t i = 0; i < n; ++i) {
        FT_UInt index = FT_Get_Char_Index(face, text[i]);
        if (!index) {error = 10001; goto done;}
        error = FT_Load_Glyph(face, index, FT_LOAD_FORCE_AUTOHINT);
        if (error) goto done;
        error = FT_Get_Glyph(face->glyph, &glyphs[i]);
        if (error) goto done;
        if (previous && FT_HAS_KERNING(face)) {
            FT_Vector delta;
            error = FT_Get_Kerning(face, previous, index, FT_KERNING_DEFAULT, &delta);
            if (error) goto done;
            pen.x += (int)delta.x / 8;
        }
        FT_Pos advance = face->glyph->advance.x;
        error = FT_Glyph_Transform(glyphs[i], NULL, &pen);
        if (error) goto done;
        FT_BBox g;
        FT_Glyph_Get_CBox(glyphs[i], FT_GLYPH_BBOX_SUBPIXELS, &g);
        if (g.xMin < bbox.xMin) bbox.xMin = g.xMin;
        if (g.xMax > bbox.xMax) bbox.xMax = g.xMax;
        if (g.yMin < bbox.yMin) bbox.yMin = g.yMin;
        if (g.yMax > bbox.yMax) bbox.yMax = g.yMax;
        pen.x += advance;
        previous = index;
    }
    if (bbox.xMin > bbox.xMax) bbox.xMin = bbox.yMin = bbox.xMax = bbox.yMax = 0;
    long width = (bbox.xMax - bbox.xMin) / 64 + 2;
    long height = (bbox.yMax - bbox.yMin) / 64 + 2;
    if (width <= 0 || height <= 0 || (size_t)width > SIZE_MAX / (size_t)height) {
        error = 10002; goto done;
    }
    *pixels = calloc((size_t)width * height, 1);
    if (!*pixels) {error = 10002; goto done;}
    for (size_t i = 0; i < n; ++i) {
        error = FT_Glyph_To_Bitmap(&glyphs[i], FT_RENDER_MODE_NORMAL, NULL, 1);
        if (error) goto done;
        FT_BitmapGlyph g = (FT_BitmapGlyph)glyphs[i];
        if (g->bitmap.pixel_mode != FT_PIXEL_MODE_GRAY) {error = 10003; goto done;}
        int x = (int)(g->left - bbox.xMin / 64.0);
        int y = (int)(bbox.yMax / 64.0 - g->top + 1);
        for (unsigned int r = 0; r < g->bitmap.rows; ++r) {
            if (y + (int)r < 0 || y + (int)r >= height) continue;
            for (unsigned int c = 0; c < g->bitmap.width; ++c) {
                if (x + (int)c < 0 || x + (int)c >= width) continue;
                (*pixels)[(y + r) * width + x + c] |= g->bitmap.buffer[r * g->bitmap.pitch + c];
            }
        }
    }
    facts[0] = width; facts[1] = height; facts[2] = pen.x;
    facts[3] = bbox.yMax - bbox.yMin; facts[4] = -bbox.yMin; facts[5] = bbox.xMin;
done:
    for (size_t i = 0; i < n; ++i) if (glyphs[i]) FT_Done_Glyph(glyphs[i]);
    free(glyphs);
    if (face) FT_Done_Face(face);
    if (library) FT_Done_FreeType(library);
    if (error) { free(*pixels); *pixels = NULL; }
    return error;
}

