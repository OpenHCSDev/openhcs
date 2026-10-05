#define PY_SSIZE_T_CLEAN
#include <Python.h>
#include <cstddef>
#include <cstring>
#include <limits>

// Keep the module entry portable: only isolated generated functions use AVX2.
#if (defined(__GNUC__) || defined(__clang__)) && (defined(__i386__) || defined(__x86_64__))
#define OPENHCS_MEDIAN_AVX2 1
#include <immintrin.h>
#else
#define OPENHCS_MEDIAN_AVX2 0
#endif
#include "_median_network_generated.h"

static bool avx2_available() {
#if OPENHCS_MEDIAN_AVX2
    // The compiler runtime checks CPUID and OS-enabled AVX register state.
    __builtin_cpu_init();
    return __builtin_cpu_supports("avx2");
#else
    return false;
#endif
}

static bool supported_window(int window) {
    for (int declared : median_windows) {
        if (declared == window) return true;
    }
    return false;
}

class ArrayBuffer {
    Py_buffer buffer_ = {};
    bool acquired_ = false;
public:
    ~ArrayBuffer() { if (acquired_) PyBuffer_Release(&buffer_); }
    bool acquire(PyObject* object, bool writable) {
        acquired_ = PyObject_GetBuffer(object, &buffer_,
            PyBUF_C_CONTIGUOUS | PyBUF_FORMAT | PyBUF_ND |
            (writable ? PyBUF_WRITABLE : 0)) == 0;
        return acquired_;
    }
    const Py_buffer& view() const { return buffer_; }
    bool validate() const {
        if (buffer_.ndim != 3 || buffer_.shape == nullptr ||
            buffer_.format == nullptr || std::strcmp(buffer_.format, "f") != 0 ||
            buffer_.itemsize != sizeof(float) || !PyBuffer_IsContiguous(&buffer_, 'C')) {
            PyErr_SetString(PyExc_ValueError, "Median buffers must be C-contiguous 3-D native float32 arrays.");
            return false;
        }
        std::size_t elements = 1;
        for (int axis = 0; axis < 3; ++axis) {
            if (buffer_.shape[axis] <= 0 ||
                static_cast<std::size_t>(buffer_.shape[axis]) >
                static_cast<std::size_t>(PY_SSIZE_T_MAX) / elements) {
                PyErr_SetString(PyExc_OverflowError, "Median buffer dimensions are empty or overflow.");
                return false;
            }
            elements *= static_cast<std::size_t>(buffer_.shape[axis]);
        }
        if (elements > static_cast<std::size_t>(PY_SSIZE_T_MAX) / sizeof(float) ||
            buffer_.len != static_cast<Py_ssize_t>(elements * sizeof(float))) {
            PyErr_SetString(PyExc_OverflowError, "Median buffer byte size is inconsistent or overflows.");
            return false;
        }
        return true;
    }
};

static PyObject* py_supported_windows(PyObject*, PyObject*) {
    const auto count = avx2_available() ? sizeof(median_windows) / sizeof(median_windows[0]) : 0;
    PyObject* result = PyTuple_New(static_cast<Py_ssize_t>(count));
    if (result == nullptr) return nullptr;
    for (std::size_t index = 0; index < count; ++index) {
        PyObject* value = PyLong_FromLong(median_windows[index]);
        if (value == nullptr) { Py_DECREF(result); return nullptr; }
        PyTuple_SetItem(result, static_cast<Py_ssize_t>(index), value);
    }
    return result;
}

static PyObject* py_filter(PyObject*, PyObject* args) {
    PyObject *input, *output;
    int window;
    if (!PyArg_ParseTuple(args, "OOi", &input, &output, &window)) return nullptr;
    if (!avx2_available() || !supported_window(window)) {
        PyErr_SetString(PyExc_ValueError, "Median network is unsupported on this CPU or footprint.");
        return nullptr;
    }
    ArrayBuffer source, target;
    if (!source.acquire(input, false) || !target.acquire(output, true) ||
        !source.validate() || !target.validate()) return nullptr;
    const auto& src = source.view();
    const auto& dst = target.view();
    const Py_ssize_t padding = window - 1;
    if (src.shape[0] <= padding || src.shape[1] <= padding || src.shape[2] <= padding + 7) {
        PyErr_SetString(PyExc_ValueError, "Median input must include constant border and vector-tail padding.");
        return nullptr;
    }
    const auto depth = src.shape[0] - padding;
    const auto height = src.shape[1] - padding;
    const auto width = src.shape[2] - padding - 7;
    // src.shape[2] already bounds width+7 without signed overflow.
    const auto output_width = ((width + 7) / 8) * 8;
    if (dst.shape[0] != depth || dst.shape[1] != height || dst.shape[2] != output_width) {
        PyErr_SetString(PyExc_ValueError, "Median output geometry does not match the padded source.");
        return nullptr;
    }
    const auto source_start = reinterpret_cast<std::size_t>(src.buf);
    const auto target_start = reinterpret_cast<std::size_t>(dst.buf);
    // Avoid addition overflow while rejecting any overlapping source/output buffers.
    if ((source_start <= target_start && target_start - source_start < static_cast<std::size_t>(src.len)) ||
        (target_start < source_start && source_start - target_start < static_cast<std::size_t>(dst.len))) {
        PyErr_SetString(PyExc_ValueError, "Median source and output buffers must be independent.");
        return nullptr;
    }
#if OPENHCS_MEDIAN_AVX2
    Py_BEGIN_ALLOW_THREADS
    run_median_network(window, static_cast<const float*>(src.buf), static_cast<float*>(dst.buf),
        static_cast<std::size_t>(depth), static_cast<std::size_t>(height), static_cast<std::size_t>(width),
        static_cast<std::size_t>(src.shape[1]), static_cast<std::size_t>(src.shape[2]),
        static_cast<std::size_t>(output_width));
    Py_END_ALLOW_THREADS
#endif
    Py_RETURN_NONE;
}

static PyMethodDef methods[] = {
    {"supported_windows", py_supported_windows, METH_NOARGS,
     "Return compiled odd footprints supported by the current CPU and OS."},
    {"filter", py_filter, METH_VARARGS,
     "Apply an exact median network to admitted padded buffers."},
    {nullptr, nullptr, 0, nullptr}
};
static PyModuleDef module = {
    PyModuleDef_HEAD_INIT, "_median_native", "Bounded exact median selection networks.", -1, methods
};
PyMODINIT_FUNC PyInit__median_native(void) { return PyModule_Create(&module); }
