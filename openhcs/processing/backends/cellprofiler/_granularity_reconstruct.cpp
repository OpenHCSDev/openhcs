#define PY_SSIZE_T_CLEAN
#include <Python.h>

#include <cstdint>
#include <cstring>
#include <limits>

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

static bool validate_array(
    const Py_buffer& view, const char* name, const char* format,
    int ndim, bool writable
) {
    if (view.ndim != ndim || view.format == nullptr ||
        std::strcmp(view.format, format) != 0 ||
        !PyBuffer_IsContiguous(&view, 'C') ||
        (writable && view.readonly)) {
        PyErr_Format(
            PyExc_ValueError,
            "%s must be a C-contiguous %d-D array with format %s%s",
            name, ndim, format, writable ? " and writable" : ""
        );
        return false;
    }
    return true;
}

static PyObject* py_reconstruct_f32(PyObject*, PyObject* args) {
    PyObject* objects[6];
    if (!PyArg_ParseTuple(
        args, "OOOOOO", &objects[0], &objects[1], &objects[2],
        &objects[3], &objects[4], &objects[5]
    )) return nullptr;

    constexpr int flags = PyBUF_C_CONTIGUOUS | PyBUF_FORMAT | PyBUF_ND;
    Py_buffer views[6] = {};
    int acquired = 0;
    for (; acquired < 6; ++acquired) {
        const int access = acquired >= 2 ? flags | PyBUF_WRITABLE : flags;
        if (PyObject_GetBuffer(objects[acquired], &views[acquired], access) < 0) {
            break;
        }
    }
    if (acquired == 6) {
        static const char* names[6] = {
            "seed", "mask", "output", "queue_rows", "queue_cols", "queued"
        };
        static const char* formats[6] = {"f", "f", "f", "I", "I", "B"};
        bool valid = true;
        for (int index = 0; index < 6 && valid; ++index) {
            valid = validate_array(
                views[index], names[index], formats[index],
                index < 3 ? 2 : 1, index >= 2
            );
        }
        if (valid) {
            const Py_ssize_t height = views[0].shape[0];
            const Py_ssize_t width = views[0].shape[1];
            const auto capacity = static_cast<unsigned long long>(height) * width;
            valid = height > 0 && width > 0 &&
                height <= std::numeric_limits<uint32_t>::max() &&
                width <= std::numeric_limits<uint32_t>::max() &&
                capacity <= std::numeric_limits<uint32_t>::max() &&
                views[1].shape[0] == height && views[1].shape[1] == width &&
                views[2].shape[0] == height && views[2].shape[1] == width &&
                views[3].shape[0] >= static_cast<Py_ssize_t>(capacity) &&
                views[4].shape[0] >= static_cast<Py_ssize_t>(capacity) &&
                views[5].shape[0] >= static_cast<Py_ssize_t>(capacity);
            if (!valid) {
                PyErr_SetString(
                    PyExc_ValueError,
                    "granularity arrays must have matching nonempty shapes and "
                    "scratch capacity for at most 2^32-1 pixels"
                );
            } else {
                Py_BEGIN_ALLOW_THREADS
                reconstruct_f32(
                    static_cast<const float*>(views[0].buf),
                    static_cast<const float*>(views[1].buf),
                    static_cast<float*>(views[2].buf),
                    static_cast<uint32_t>(height), static_cast<uint32_t>(width),
                    static_cast<uint32_t*>(views[3].buf),
                    static_cast<uint32_t*>(views[4].buf),
                    static_cast<uint8_t*>(views[5].buf)
                );
                Py_END_ALLOW_THREADS
            }
        }
    }
    for (int index = 0; index < acquired; ++index) {
        PyBuffer_Release(&views[index]);
    }
    if (PyErr_Occurred()) return nullptr;
    Py_RETURN_NONE;
}

static PyMethodDef methods[] = {
    {"reconstruct_f32", py_reconstruct_f32, METH_VARARGS,
     "Reconstruct a C-contiguous float32 image with caller-owned scratch."},
    {nullptr, nullptr, 0, nullptr}
};

static PyModuleDef module = {
    PyModuleDef_HEAD_INIT,
    "_granularity_reconstruct",
    "Exact single-thread CellProfiler granularity reconstruction.",
    -1,
    methods
};

PyMODINIT_FUNC PyInit__granularity_reconstruct(void) {
    return PyModule_Create(&module);
}
