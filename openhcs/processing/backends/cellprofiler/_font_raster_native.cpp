// Stable-ABI binding; the linked FreeType engine has no exported symbols.
#define PY_SSIZE_T_CLEAN
#include <Python.h>
#include <cmath>
#include <climits>
#include <cstdint>
#include <cstdlib>
#include <vector>

extern "C" int openhcs_render_text(const char *, double, double,
                                 const uint32_t *, size_t, unsigned char **, long *);

static PyObject *rasterize(PyObject *, PyObject *args) {
    const char *path;
    double points, dpi;
    PyObject *text;
    if (!PyArg_ParseTuple(args, "sddU:rasterize", &path, &points, &dpi, &text))
        return nullptr;
    if (!std::isfinite(points) || !std::isfinite(dpi) || points <= 0 || dpi <= 0 ||
        points > LONG_MAX / 64.0 || dpi > UINT_MAX / 8.0) {
        PyErr_SetString(PyExc_ValueError, "Font size and DPI must be finite positive representable values");
        return nullptr;
    }
    Py_ssize_t length = PyUnicode_GetLength(text);
    if (length < 0) return nullptr;
    std::vector<uint32_t> codepoints;
    try {
        codepoints.reserve(length);
        for (Py_ssize_t i = 0; i < length; ++i) {
            Py_UCS4 value = PyUnicode_ReadChar(text, i);
            if (value == static_cast<Py_UCS4>(-1) && PyErr_Occurred()) return nullptr;
            codepoints.push_back(value);
        }
    } catch (const std::bad_alloc &) { return PyErr_NoMemory(); }
    unsigned char *pixels = nullptr;
    long facts[6];
    int error = openhcs_render_text(path, points, dpi, codepoints.data(),
                                   codepoints.size(), &pixels, facts);
    if (error) {
        if (error == 10002) return PyErr_NoMemory();
        PyErr_Format(PyExc_ValueError, "CellProfiler font rasterization failed (FreeType error %d)", error);
        return nullptr;
    }
    if (facts[0] <= 0 || facts[1] <= 0 || facts[0] > PY_SSIZE_T_MAX / facts[1]) {
        std::free(pixels);
        return PyErr_NoMemory();
    }
    PyObject *bitmap = PyByteArray_FromStringAndSize(reinterpret_cast<char *>(pixels), facts[0] * facts[1]);
    std::free(pixels);
    if (!bitmap) return nullptr;
    PyObject *result = Py_BuildValue("N(llllll)", bitmap, facts[0], facts[1], facts[2], facts[3], facts[4], facts[5]);
    return result;
}

static PyMethodDef methods[] = {
    {"rasterize", rasterize, METH_VARARGS, "Rasterize a complete plaintext string with CellProfiler's font metrics."},
    {nullptr, nullptr, 0, nullptr}
};
static PyModuleDef module = {
    PyModuleDef_HEAD_INIT, "_font_raster_native", nullptr, -1, methods,
    nullptr, nullptr, nullptr, nullptr
};
PyMODINIT_FUNC PyInit__font_raster_native() { return PyModule_Create(&module); }
