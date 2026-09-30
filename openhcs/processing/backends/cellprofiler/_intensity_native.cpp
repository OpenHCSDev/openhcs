#define PY_SSIZE_T_CLEAN
#include <Python.h>
#include "native_array_buffer.hpp"

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <limits>

// CP uses count * fraction, including its neighbor even at zero weight.
// Keep NaNs last, as in NumPy partition, for overflow in MAD deviations.
static bool less_value(double left, double right) {
    if (std::isnan(right)) return !std::isnan(left);
    return left < right;
}

static void select_ranks(
    double* values, const int64_t* ranks, int first, int stop,
    int64_t left, int64_t right
) {
    if (first >= stop) return;
    const int middle = (first + stop) / 2;
    const int64_t rank = ranks[middle];
    std::nth_element(values + left, values + rank, values + right + 1, less_value);
    int low = middle, high = middle + 1;
    while (low > first && ranks[low - 1] == rank) --low;
    while (high < stop && ranks[high] == rank) ++high;
    select_ranks(values, ranks, first, low, left, rank - 1);
    select_ranks(values, ranks, high, stop, rank + 1, right);
}

static double quantile(const double* values, int64_t count, double fraction) {
    const double index = count * fraction;
    const int64_t low = static_cast<int64_t>(index);
    const double weight = index - low;
    if (low >= count - 1) return values[count - 1];
    return values[low] * (1.0 - weight) + values[low + 1] * weight;
}

static void group_quantiles(
    double* values, int64_t count, double mad_fraction,
    double& lower, double& median, double& upper, double& mad
) {
    int64_t ranks[6];
    int position = 0;
    for (double fraction : {0.25, 0.5, 0.75}) {
        const int64_t low = static_cast<int64_t>(count * fraction);
        ranks[position++] = std::min(low, count - 1);
        ranks[position++] = std::min(low + 1, count - 1);
    }
    select_ranks(values, ranks, 0, 6, 0, count - 1);
    lower = quantile(values, count, 0.25);
    median = quantile(values, count, 0.5);
    upper = quantile(values, count, 0.75);
    for (int64_t index = 0; index < count; ++index)
        values[index] = std::abs(values[index] - median);
    const int64_t low = static_cast<int64_t>(count * mad_fraction);
    const int64_t mad_ranks[2] = {
        std::min(low, count - 1), std::min(low + 1, count - 1)
    };
    select_ranks(values, mad_ranks, 0, 2, 0, count - 1);
    mad = quantile(values, count, mad_fraction);
}

static bool valid_buffer(
    const OwnedArrayBuffer& buffer, const char* name, bool offsets
) {
    const Py_buffer& view = buffer.view();
    const char* format = offsets && view.format != nullptr &&
        std::strcmp(view.format, "q") == 0 ? "q" : offsets ? "l" : "d";
    if (!buffer.matches(name, format, 1, !offsets)) return false;
    const size_t alignment = offsets ? alignof(int64_t) : alignof(double);
    if (view.itemsize != 8 || view.shape[0] < 0 ||
        view.shape[0] > PY_SSIZE_T_MAX / 8 || view.len != view.shape[0] * 8 ||
        (view.len > 0 && (view.buf == nullptr ||
            reinterpret_cast<uintptr_t>(view.buf) % alignment != 0))) {
        PyErr_Format(PyExc_ValueError, "%s must have aligned 64-bit elements", name);
        return false;
    }
    return true;
}

static bool buffers_are_disjoint(const OwnedArrayBuffer* buffers) {
    for (int first = 0; first < 6; ++first) {
        const Py_buffer& left = buffers[first].view();
        if (left.len == 0) continue;
        const uintptr_t left_start = reinterpret_cast<uintptr_t>(left.buf);
        for (int second = first + 1; second < 6; ++second) {
            const Py_buffer& right = buffers[second].view();
            if (right.len == 0) continue;
            const uintptr_t right_start = reinterpret_cast<uintptr_t>(right.buf);
            // Compare distances to avoid overflow when computing end addresses.
            const bool overlap = left_start <= right_start
                ? right_start - left_start < static_cast<uintptr_t>(left.len)
                : left_start - right_start < static_cast<uintptr_t>(right.len);
            if (overlap) {
                PyErr_SetString(PyExc_ValueError, "quantile buffers must not overlap");
                return false;
            }
        }
    }
    return true;
}

static PyObject* py_grouped_quantiles(PyObject*, PyObject* args) {
    PyObject* objects[6];
    double mad_fraction;
    if (!PyArg_ParseTuple(
        args, "OOOOOOd", &objects[0], &objects[1], &objects[2],
        &objects[3], &objects[4], &objects[5], &mad_fraction
    )) return nullptr;
    if (!std::isfinite(mad_fraction) || mad_fraction < 0 || mad_fraction > 1) {
        PyErr_SetString(PyExc_ValueError, "MAD fraction must be finite and in [0, 1]");
        return nullptr;
    }
    static const char* names[6] = {
        "values", "offsets", "lower", "median", "upper", "mad"
    };
    OwnedArrayBuffer buffers[6];
    for (int index = 0; index < 6; ++index) {
        if (!buffers[index].acquire(objects[index], index != 1) ||
            !valid_buffer(buffers[index], names[index], index == 1)) return nullptr;
    }
    if (!buffers_are_disjoint(buffers)) return nullptr;
    const Py_ssize_t offset_count = buffers[1].view().shape[0];
    if (offset_count < 1) {
        PyErr_SetString(PyExc_ValueError, "offsets must include a starting zero");
        return nullptr;
    }
    const Py_ssize_t groups = offset_count - 1;
    for (int index = 2; index < 6; ++index) {
        if (buffers[index].view().shape[0] != groups) {
            PyErr_SetString(PyExc_ValueError, "output sizes must match the group count");
            return nullptr;
        }
    }
    const int64_t* offsets = static_cast<const int64_t*>(buffers[1].view().buf);
    const Py_ssize_t value_count = buffers[0].view().shape[0];
    if (offsets[0] != 0 || offsets[groups] != value_count) {
        PyErr_SetString(PyExc_ValueError, "offsets must span the complete values buffer");
        return nullptr;
    }
    for (Py_ssize_t index = 1; index < offset_count; ++index) {
        if (offsets[index] < offsets[index - 1] || offsets[index] > value_count) {
            PyErr_SetString(PyExc_ValueError, "offsets must be nondecreasing and in bounds");
            return nullptr;
        }
    }
    double* values = static_cast<double*>(buffers[0].view().buf);
    double* lower = static_cast<double*>(buffers[2].view().buf);
    double* median = static_cast<double*>(buffers[3].view().buf);
    double* upper = static_cast<double*>(buffers[4].view().buf);
    double* mad = static_cast<double*>(buffers[5].view().buf);
    Py_BEGIN_ALLOW_THREADS
    for (Py_ssize_t group = 0; group < groups; ++group) {
        lower[group] = median[group] = upper[group] = mad[group] = 0;
        const int64_t count = offsets[group + 1] - offsets[group];
        if (count != 0) group_quantiles(
            values + offsets[group], count, mad_fraction,
            lower[group], median[group], upper[group], mad[group]
        );
    }
    Py_END_ALLOW_THREADS
    Py_RETURN_NONE;
}

static PyMethodDef methods[] = {
    {"grouped_quantiles", py_grouped_quantiles, METH_VARARGS,
        "Write CP quartiles and MAD from an owned grouped-values workspace."},
    {nullptr, nullptr, 0, nullptr}
};

static PyModuleDef module = {
    PyModuleDef_HEAD_INIT, "_intensity_native", nullptr, -1, methods
};

PyMODINIT_FUNC PyInit__intensity_native() { return PyModule_Create(&module); }
