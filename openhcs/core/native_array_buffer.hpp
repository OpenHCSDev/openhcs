#pragma once

#include <Python.h>
#include <cstring>

class OwnedArrayBuffer {
    Py_buffer view_ = {};
    bool acquired_ = false;
public:
    OwnedArrayBuffer() = default;
    OwnedArrayBuffer(const OwnedArrayBuffer&) = delete;
    OwnedArrayBuffer& operator=(const OwnedArrayBuffer&) = delete;
    ~OwnedArrayBuffer() {
        if (acquired_) PyBuffer_Release(&view_);
    }
    bool acquire(PyObject* object, bool writable) {
        const int flags = PyBUF_C_CONTIGUOUS | PyBUF_FORMAT | PyBUF_ND |
            (writable ? PyBUF_WRITABLE : 0);
        acquired_ = PyObject_GetBuffer(object, &view_, flags) == 0;
        return acquired_;
    }
    const Py_buffer& view() const { return view_; }
    bool matches(const char* name, const char* format, int ndim, bool writable) const {
        if (view_.ndim != ndim || view_.format == nullptr || format == nullptr ||
            std::strcmp(view_.format, format) != 0 ||
            !PyBuffer_IsContiguous(&view_, 'C') || (writable && view_.readonly)) {
            PyErr_Format(PyExc_ValueError,
                "%s must be a C-contiguous %d-D array with format %s%s",
                name, ndim, format == nullptr ? "(declared)" : format,
                writable ? " and writable" : "");
            return false;
        }
        return true;
    }
};
