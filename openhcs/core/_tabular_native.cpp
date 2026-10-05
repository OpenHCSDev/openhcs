#define PY_SSIZE_T_CLEAN
#include <Python.h>
#include <cmath>
#include <new>
#include <stdexcept>
#include <string>
#include <vector>

class OwnedPyObject {
    PyObject *value;

  public:
    explicit OwnedPyObject(PyObject *object) : value(object) {}
    ~OwnedPyObject() { Py_XDECREF(value); }
    OwnedPyObject(const OwnedPyObject &) = delete;
    OwnedPyObject &operator=(const OwnedPyObject &) = delete;
    OwnedPyObject(OwnedPyObject &&other) noexcept : value(other.value) { other.value = nullptr; }
    OwnedPyObject &operator=(OwnedPyObject &&other) noexcept {
        if (this != &other) {
            Py_XDECREF(value);
            value = other.value;
            other.value = nullptr;
        }
        return *this;
    }
    PyObject *get() const { return value; }
};

static bool append_csv_cell(std::string &output, PyObject *value, char delimiter,
                            bool single_cell) {
    OwnedPyObject text(value == Py_None
                           ? PyUnicode_FromString("")
                           : (PyUnicode_Check(value) ? Py_NewRef(value) : PyObject_Str(value)));
    if (!text.get())
        return false;
    OwnedPyObject encoded(PyUnicode_AsEncodedString(text.get(), "utf-8", "surrogatepass"));
    if (!encoded.get())
        return false;
    char *data = nullptr;
    Py_ssize_t size = 0;
    if (PyBytes_AsStringAndSize(encoded.get(), &data, &size) < 0)
        return false;
    bool quoted = single_cell && size == 0;
    for (Py_ssize_t i = 0; i < size && !quoted; ++i)
        quoted = data[i] == delimiter || data[i] == '"' || data[i] == '\n' || data[i] == '\r';
    if (!quoted) {
        output.append(data, static_cast<size_t>(size));
        return true;
    }
    output.push_back('"');
    for (Py_ssize_t i = 0; i < size; ++i) {
        if (data[i] == '"')
            output.push_back('"');
        output.push_back(data[i]);
    }
    output.push_back('"');
    return true;
}

class CsvScalarNormalization {
    PyObject *real_class;
    bool null_nonfinite;
    OwnedPyObject empty, nan, positive_inf, negative_inf;

  public:
    CsvScalarNormalization(PyObject *type, bool nulls)
        : real_class(type), null_nonfinite(nulls), empty(PyUnicode_FromString("")),
          nan(PyUnicode_FromString("NaN")), positive_inf(PyUnicode_FromString("Inf")),
          negative_inf(PyUnicode_FromString("-Inf")) {}
    bool ready() const {
        return empty.get() && nan.get() && positive_inf.get() && negative_inf.get();
    }
    PyObject *empty_value() const { return empty.get(); }
    PyObject *normalize(PyObject *value) const {
        if (!PyBool_Check(value)) {
            double number = 0;
            bool numeric = false;
            if (PyFloat_CheckExact(value)) {
                number = PyFloat_AsDouble(value);
                numeric = true;
            } else if (PyLong_CheckExact(value)) {
                number = PyLong_AsDouble(value);
                numeric = true;
            } else {
                int real = (PyFloat_Check(value) || PyLong_Check(value))
                               ? 1
                               : PyObject_IsInstance(value, real_class);
                if (real < 0)
                    return nullptr;
                if (real) {
                    OwnedPyObject normalized(PyNumber_Float(value));
                    if (!normalized.get())
                        return nullptr;
                    number = PyFloat_AsDouble(normalized.get());
                    numeric = true;
                }
            }
            if (PyErr_Occurred())
                return nullptr;
            if (numeric && !std::isfinite(number)) {
                return Py_NewRef(null_nonfinite
                                     ? empty.get()
                                     : (std::isnan(number) ? nan.get()
                                                           : (number > 0 ? positive_inf.get()
                                                                         : negative_inf.get())));
            }
        }
        return Py_NewRef(value);
    }
};

static PyObject *render_csv(PyObject *, PyObject *args) {
    PyObject *rows, *columns, *real_class;
    PyObject *header_rows = Py_None;
    const char *delimiter;
    int null_nonfinite;
    if (!PyArg_ParseTuple(args, "OOsOp|O", &rows, &columns, &delimiter, &real_class,
                          &null_nonfinite, &header_rows))
        return nullptr;
    if (!PyTuple_Check(rows) || !PyTuple_Check(columns)) {
        PyErr_SetString(PyExc_TypeError, "Rows and columns must be tuples");
        return nullptr;
    }
    if (delimiter[0] == '\0' || delimiter[1] != '\0') {
        PyErr_SetString(PyExc_ValueError, "CSV delimiter must be one ASCII character");
        return nullptr;
    }
    Py_ssize_t column_count = PyTuple_Size(columns), row_count = PyTuple_Size(rows);
    if (column_count == 0)
        return PyUnicode_FromString("");
    if (header_rows != Py_None) {
        if (!PyTuple_Check(header_rows)) {
            PyErr_SetString(PyExc_TypeError, "CSV header rows must be tuples");
            return nullptr;
        }
        for (Py_ssize_t index = 0; index < PyTuple_Size(header_rows); ++index) {
            PyObject *header = PyTuple_GetItem(header_rows, index);
            if (!PyTuple_Check(header) || PyTuple_Size(header) != column_count) {
                PyErr_SetString(PyExc_ValueError, "CSV header width must match columns");
                return nullptr;
            }
        }
    }
    try {
        std::string output;
        output.reserve(static_cast<size_t>(row_count) * static_cast<size_t>(column_count) * 10);
        Py_ssize_t header_count = header_rows == Py_None ? 1 : PyTuple_Size(header_rows);
        for (Py_ssize_t index = 0; index < header_count; ++index) {
            PyObject *header = header_rows == Py_None ? columns : PyTuple_GetItem(header_rows, index);
            for (Py_ssize_t col = 0; col < column_count; ++col) {
                if (col)
                    output.push_back(delimiter[0]);
                if (!append_csv_cell(output, PyTuple_GetItem(header, col), delimiter[0],
                                     column_count == 1))
                    return nullptr;
            }
            output.push_back('\n');
        }
        CsvScalarNormalization normalization(real_class, null_nonfinite);
        if (!normalization.ready())
            return nullptr;
        std::vector<OwnedPyObject> cells;
        cells.reserve(static_cast<size_t>(column_count));
        for (Py_ssize_t index = 0; index < row_count; ++index) {
            PyObject *row = PyTuple_GetItem(rows, index);
            cells.clear();
            for (Py_ssize_t col = 0; col < column_count; ++col) {
                PyObject *key = PyTuple_GetItem(columns, col);
                OwnedPyObject value(
                    PyDict_CheckExact(row)
                        ? Py_XNewRef(PyDict_GetItemWithError(row, key))
                        : PyObject_CallMethod(row, "get", "OO", key, normalization.empty_value()));
                if (!value.get() && PyErr_Occurred())
                    return nullptr;
                PyObject *normalized = normalization.normalize(
                    value.get() ? value.get() : normalization.empty_value());
                if (!normalized)
                    return nullptr;
                cells.emplace_back(normalized);
            }
            for (Py_ssize_t col = 0; col < column_count; ++col) {
                if (col)
                    output.push_back(delimiter[0]);
                if (!append_csv_cell(output, cells[static_cast<size_t>(col)].get(), delimiter[0],
                                     column_count == 1))
                    return nullptr;
            }
            output.push_back('\n');
        }
        return PyUnicode_DecodeUTF8(output.data(), static_cast<Py_ssize_t>(output.size()),
                                    "surrogatepass");
    } catch (const std::bad_alloc &) {
        return PyErr_NoMemory();
    } catch (const std::length_error &) {
        PyErr_SetString(PyExc_OverflowError, "CSV output exceeds addressable memory");
        return nullptr;
    }
}
static bool assign_cell(PyObject *target, PyObject *identity, PyObject *field, PyObject *value,
                        PyObject *missing, PyObject *equality) {
    OwnedPyObject existing(PyDict_CheckExact(target)
                               ? Py_XNewRef(PyDict_GetItemWithError(target, field))
                               : PyObject_CallMethod(target, "get", "OO", field, missing));
    if (!existing.get() && PyErr_Occurred())
        return false;
    if (existing.get() && existing.get() != missing) {
        OwnedPyObject same(PyObject_CallFunctionObjArgs(equality, existing.get(), value, nullptr));
        if (!same.get())
            return false;
        int is_same = PyObject_IsTrue(same.get());
        if (is_same < 0)
            return false;
        if (!is_same) {
            PyErr_Format(
                PyExc_ValueError,
                "Conflicting sparse measurement values for row identity %R, field %R: %R vs %R.",
                identity, field, existing.get(), value);
            return false;
        }
    }
    return (PyDict_CheckExact(target) ? PyDict_SetItem(target, field, value)
                                      : PyObject_SetItem(target, field, value)) == 0;
}

static PyObject *py_assign_cell(PyObject *, PyObject *args) {
    PyObject *target, *identity, *field, *value, *missing, *equality;
    if (!PyArg_ParseTuple(args, "OOOOOO", &target, &identity, &field, &value, &missing, &equality))
        return nullptr;
    if (!assign_cell(target, identity, field, value, missing, equality))
        return nullptr;
    Py_RETURN_NONE;
}

static PyObject *py_assign_columns(PyObject *, PyObject *args) {
    PyObject *target, *identity, *columns, *index, *project_feature, *qualifiers, *missing_type,
        *missing, *equality;
    if (!PyArg_ParseTuple(args, "OOOOOOOOO", &target, &identity, &columns, &index, &project_feature,
                          &qualifiers, &missing_type, &missing, &equality))
        return nullptr;
    if (!PyTuple_Check(columns)) {
        PyErr_SetString(PyExc_TypeError, "Feature columns must be a tuple");
        return nullptr;
    }
    Py_ssize_t count = PyTuple_Size(columns);
    for (Py_ssize_t col = 0; col < count; ++col) {
        PyObject *column = PyTuple_GetItem(columns, col);
        if (!PyTuple_Check(column) || PyTuple_Size(column) != 2) {
            PyErr_SetString(PyExc_TypeError, "Feature column must be a name/value pair");
            return nullptr;
        }
        PyObject *name = PyTuple_GetItem(column, 0);
        OwnedPyObject value(PyObject_GetItem(PyTuple_GetItem(column, 1), index));
        if (!value.get())
            return nullptr;
        int is_missing = PyObject_IsInstance(value.get(), missing_type);
        if (is_missing < 0)
            return nullptr;
        if (is_missing)
            continue;
        OwnedPyObject field(
            PyObject_CallFunctionObjArgs(project_feature, name, qualifiers, nullptr));
        if (!field.get() ||
            !assign_cell(target, identity, field.get(), value.get(), missing, equality))
            return nullptr;
    }
    Py_RETURN_NONE;
}
static PyMethodDef methods[] = {
    {"assign_cell", py_assign_cell, METH_VARARGS,
     "Assign one measurement cell with shared conflict policy."},
    {"assign_columns", py_assign_columns, METH_VARARGS,
     "Assign one row of declared feature columns."},
    {"render_csv", render_csv, METH_VARARGS,
     "Render admitted spreadsheet rows with exact Python value strings."},
    {nullptr, nullptr, 0, nullptr}};
static PyModuleDef module = {PyModuleDef_HEAD_INIT, "_tabular_native", nullptr, -1, methods};
PyMODINIT_FUNC PyInit__tabular_native(void) { return PyModule_Create(&module); }
