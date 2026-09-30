#define PY_SSIZE_T_CLEAN
#include <Python.h>
#include "native_array_buffer.hpp"

#include <cstdint>
#include <cmath>
#include <cstring>
#include <limits>
#include <type_traits>

static inline void enqueue(
    uint32_t row, uint32_t col, uint32_t index,
    uint32_t* qr, uint32_t* qc, uint8_t* queued,
    uint32_t& tail, uint32_t& count, uint32_t capacity
) {
    if (queued[index]) return;
    queued[index] = 1;
    qr[tail] = row;
    qc[tail] = col;
    ++tail;
    if (tail == capacity) tail = 0;
    ++count;
}

static inline void update_neighbor(
    float* out, const float* mask,
    uint32_t row, uint32_t col, uint32_t width,
    float source_value,
    uint32_t* qr, uint32_t* qc, uint8_t* queued,
    uint32_t& tail, uint32_t& count, uint32_t capacity
) {
    const uint32_t index = row * width + col;
    float candidate = source_value;
    if (candidate > mask[index]) candidate = mask[index];
    if (candidate <= out[index]) return;
    out[index] = candidate;
    enqueue(row, col, index, qr, qc, queued, tail, count, capacity);
}

static void reconstruct_f32(
    const float* __restrict seed,
    const float* __restrict mask,
    float* __restrict out,
    uint32_t height, uint32_t width,
    uint32_t* __restrict qr,
    uint32_t* __restrict qc,
    uint8_t* __restrict queued
) {
    const uint32_t capacity = height * width;
    std::memcpy(out, seed, capacity * sizeof(float));
    std::memset(queued, 0, capacity);
    for (uint32_t row = 0; row < height; ++row) {
        const uint32_t base = row * width;
        for (uint32_t col = 0; col < width; ++col) {
            const uint32_t index = base + col;
            float value = out[index];
            if (row > 0 && out[index - width] > value) value = out[index - width];
            if (col > 0 && out[index - 1] > value) value = out[index - 1];
            if (value > mask[index]) value = mask[index];
            out[index] = value;
        }
    }
    uint32_t head = 0, tail = 0, count = 0;
    for (uint32_t row = height; row-- > 0;) {
        const uint32_t base = row * width;
        for (uint32_t col = width; col-- > 0;) {
            const uint32_t index = base + col;
            float value = out[index];
            if (row + 1 < height && out[index + width] > value) value = out[index + width];
            if (col + 1 < width && out[index + 1] > value) value = out[index + 1];
            if (value > mask[index]) value = mask[index];
            out[index] = value;
            bool can_raise = false;
            if (row > 0 && out[index - width] < value && out[index - width] < mask[index - width]) can_raise = true;
            if (row + 1 < height && out[index + width] < value && out[index + width] < mask[index + width]) can_raise = true;
            if (col > 0 && out[index - 1] < value && out[index - 1] < mask[index - 1]) can_raise = true;
            if (col + 1 < width && out[index + 1] < value && out[index + 1] < mask[index + 1]) can_raise = true;
            if (can_raise) enqueue(row, col, index, qr, qc, queued, tail, count, capacity);
        }
    }
    while (count > 0) {
        const uint32_t row = qr[head];
        const uint32_t col = qc[head];
        const uint32_t index = row * width + col;
        queued[index] = 0;
        ++head;
        if (head == capacity) head = 0;
        --count;
        const float value = out[index];
        if (row > 0) update_neighbor(out, mask, row - 1, col, width, value, qr, qc, queued, tail, count, capacity);
        if (row + 1 < height) update_neighbor(out, mask, row + 1, col, width, value, qr, qc, queued, tail, count, capacity);
        if (col > 0) update_neighbor(out, mask, row, col - 1, width, value, qr, qc, queued, tail, count, capacity);
        if (col + 1 < width) update_neighbor(out, mask, row, col + 1, width, value, qr, qc, queued, tail, count, capacity);
    }
}

static PyObject* py_reconstruct_f32(PyObject*, PyObject* args) {
    PyObject* objects[6];
    if (!PyArg_ParseTuple(
        args, "OOOOOO", &objects[0], &objects[1], &objects[2],
        &objects[3], &objects[4], &objects[5]
    )) return nullptr;

    OwnedArrayBuffer buffers[6];
    int acquired = 0;
    for (; acquired < 6; ++acquired) {
        if (!buffers[acquired].acquire(objects[acquired], acquired >= 2)) break;
    }
    if (acquired == 6) {
        static const char* names[6] = {
            "seed", "mask", "output", "queue_rows", "queue_cols", "queued"
        };
        static const char* formats[6] = {"f", "f", "f", "I", "I", "B"};
        bool valid = true;
        for (int index = 0; index < 6 && valid; ++index) {
            valid = buffers[index].matches(
                names[index], formats[index],
                index < 3 ? 2 : 1, index >= 2
            );
        }
        if (valid) {
            const Py_ssize_t height = buffers[0].view().shape[0];
            const Py_ssize_t width = buffers[0].view().shape[1];
            const auto capacity = static_cast<unsigned long long>(height) * width;
            valid = height > 0 && width > 0 &&
                height <= std::numeric_limits<uint32_t>::max() &&
                width <= std::numeric_limits<uint32_t>::max() &&
                capacity <= std::numeric_limits<uint32_t>::max() &&
                buffers[1].view().shape[0] == height && buffers[1].view().shape[1] == width &&
                buffers[2].view().shape[0] == height && buffers[2].view().shape[1] == width &&
                buffers[3].view().shape[0] >= static_cast<Py_ssize_t>(capacity) &&
                buffers[4].view().shape[0] >= static_cast<Py_ssize_t>(capacity) &&
                buffers[5].view().shape[0] >= static_cast<Py_ssize_t>(capacity);
            if (!valid) {
                PyErr_SetString(
                    PyExc_ValueError,
                    "granularity arrays must have matching nonempty shapes and "
                    "scratch capacity for at most 2^32-1 pixels"
                );
            } else {
                Py_BEGIN_ALLOW_THREADS
                reconstruct_f32(
                    static_cast<const float*>(buffers[0].view().buf),
                    static_cast<const float*>(buffers[1].view().buf),
                    static_cast<float*>(buffers[2].view().buf),
                    static_cast<uint32_t>(height), static_cast<uint32_t>(width),
                    static_cast<uint32_t*>(buffers[3].view().buf),
                    static_cast<uint32_t*>(buffers[4].view().buf),
                    static_cast<uint8_t*>(buffers[5].view().buf)
                );
                Py_END_ALLOW_THREADS
            }
        }
    }
    if (PyErr_Occurred()) return nullptr;
    Py_RETURN_NONE;
}

template<class T>
static T cast_sample(double value) {
    if (std::is_integral<T>::value) {
        // Match the native CP reference's half rounding and strict bounds.
        value = value > 0 ? value + 0.5 : value - 0.5;
        if (value > std::numeric_limits<T>::max())
            value = std::numeric_limits<T>::max();
        if (value < std::numeric_limits<T>::lowest())
            value = std::numeric_limits<T>::lowest();
    }
    return static_cast<T>(value);
}

template<class T, bool Boolean = false>
static bool sample_grid(
    const Py_buffer& image, const Py_buffer& output,
    double row_scale, double column_scale
) {
    if (image.itemsize != sizeof(T) || output.itemsize != sizeof(T)) return false;
    const T* source = static_cast<const T*>(image.buf);
    T* target = static_cast<T*>(output.buf);
    const Py_ssize_t height = image.shape[0], width = image.shape[1];
    const Py_ssize_t rows = output.shape[0], columns = output.shape[1];
    for (Py_ssize_t row = 0; row < rows; ++row) {
        const double y = row * row_scale;
        for (Py_ssize_t column = 0; column < columns; ++column) {
            const double x = column * column_scale;
            double value = 0;
            if (std::isfinite(y) && std::isfinite(x) &&
                y >= 0 && x >= 0 && y <= height - 1 && x <= width - 1) {
                const auto y0 = static_cast<Py_ssize_t>(y);
                const auto x0 = static_cast<Py_ssize_t>(x);
                // Constant coordinates use a mirrored spline footprint at the
                // final cell. Zero-weight NaN/Inf neighbors still participate.
                const auto y1 = y0 + 1 < height ? y0 + 1 : (height > 1 ? height - 2 : 0);
                const auto x1 = x0 + 1 < width ? x0 + 1 : (width > 1 ? width - 2 : 0);
                const double wy0 = 1 - (y - y0), wx0 = 1 - (x - x0);
                const double wy1 = 1 - wy0, wx1 = 1 - wx0;
                value = static_cast<double>(source[y0 * width + x0]) * wy0 * wx0;
                value += static_cast<double>(source[y0 * width + x1]) * wy0 * wx1;
                value += static_cast<double>(source[y1 * width + x0]) * wy1 * wx0;
                value += static_cast<double>(source[y1 * width + x1]) * wy1 * wx1;
            }
            target[row * columns + column] = Boolean ? static_cast<T>(value) : cast_sample<T>(value);
        }
    }
    return true;
}

static PyObject* py_sample_order_one_grid(PyObject*, PyObject* args) {
    PyObject *image, *output;
    double row_scale, column_scale;
    if (!PyArg_ParseTuple(
        args, "OOdd", &image, &output, &row_scale, &column_scale
    )) return nullptr;
    OwnedArrayBuffer image_buffer, output_buffer;
    if (!image_buffer.acquire(image, false) || !output_buffer.acquire(output, true)) return nullptr;
    const auto& input_view = image_buffer.view();
    const auto& output_view = output_buffer.view();
    if (!image_buffer.matches("image", input_view.format, 2, false) ||
        !output_buffer.matches("output", input_view.format, 2, true)) return nullptr;
    bool valid = input_view.format[1] == '\0';
    if (valid) {
        Py_BEGIN_ALLOW_THREADS
        switch (input_view.format[0]) {
            case 'f':
                valid = sample_grid<float>(input_view, output_view, row_scale, column_scale);
                break;
            case 'd':
                valid = sample_grid<double>(input_view, output_view, row_scale, column_scale);
                break;
            case '?':
                valid = sample_grid<unsigned char,true>(input_view, output_view, row_scale, column_scale);
                break;
            case 'b':
                valid = sample_grid<signed char>(input_view, output_view, row_scale, column_scale);
                break;
            case 'B':
                valid = sample_grid<unsigned char>(input_view, output_view, row_scale, column_scale);
                break;
            case 'h':
                valid = sample_grid<short>(input_view, output_view, row_scale, column_scale);
                break;
            case 'H':
                valid = sample_grid<unsigned short>(input_view, output_view, row_scale, column_scale);
                break;
            case 'i':
                valid = sample_grid<int>(input_view, output_view, row_scale, column_scale);
                break;
            case 'I':
                valid = sample_grid<unsigned int>(input_view, output_view, row_scale, column_scale);
                break;
            case 'l':
                valid = sample_grid<long>(input_view, output_view, row_scale, column_scale);
                break;
            case 'L':
                valid = sample_grid<unsigned long>(input_view, output_view, row_scale, column_scale);
                break;
            case 'q':
                valid = sample_grid<long long>(input_view, output_view, row_scale, column_scale);
                break;
            case 'Q':
                valid = sample_grid<unsigned long long>(input_view, output_view, row_scale, column_scale);
                break;
            default:
                valid = false;
        }
        Py_END_ALLOW_THREADS
    }
    if (!valid) {
        PyErr_SetString(PyExc_RuntimeError, "data type not supported");
        return nullptr;
    }
    Py_RETURN_NONE;
}

static PyMethodDef methods[] = {
    {"sample_order_one_grid", py_sample_order_one_grid, METH_VARARGS,
     "Sample constant-zero order-one coordinates into a caller-owned grid."},
    {"reconstruct_f32", py_reconstruct_f32, METH_VARARGS,
     "Reconstruct a C-contiguous float32 image with caller-owned scratch."},
    {nullptr, nullptr, 0, nullptr}
};

static PyModuleDef module = {
    PyModuleDef_HEAD_INIT,
    "_granularity_native",
    "Exact single-thread CellProfiler granularity reconstruction and sampling.",
    -1,
    methods
};

PyMODINIT_FUNC PyInit__granularity_native(void) {
    return PyModule_Create(&module);
}
