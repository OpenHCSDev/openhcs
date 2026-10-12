"""Record every arraybridge conversion a process performs, and how it was done.

OpenHCS converts image payloads between array libraries through
``arraybridge.MemoryType.convert_to``. That method tries DLPack first (the array
stays on its device and the two libraries share one buffer) and falls back to a
copy through host memory. It logs only the fallback. This module wraps the
conversion methods so each call appends one JSON line to the file named by the
``OPENHCS_CONVERSION_TRACE`` environment variable: source and target library,
shape, bytes, the route taken (``same``, ``dlpack`` or ``host``), whether the
result shares the source buffer, and the time spent.

It is a diagnostic for the GPU check, installed by the neighbouring
``sitecustomize.py`` so that it is active in the execution server and in every
worker process. It changes no behaviour.
"""

from __future__ import annotations

import json
import os
import sys
import threading
import time

from arraybridge import MemoryType

_STATE = threading.local()
_LOCK = threading.Lock()


def _buffer_address(data) -> int | None:
    """Address of the first element, on whichever device holds it."""
    try:
        if hasattr(data, "data_ptr"):  # torch
            return int(data.data_ptr())
        if hasattr(data, "__cuda_array_interface__"):  # cupy and other CUDA arrays
            return int(data.__cuda_array_interface__["data"][0])
        if hasattr(data, "__array_interface__"):  # numpy
            return int(data.__array_interface__["data"][0])
    except Exception:
        return None
    return None


def _device(data) -> str:
    device = getattr(data, "device", None)
    if device is None:
        return "cpu"
    if hasattr(device, "id"):  # cupy
        return f"cuda:{device.id}"
    return str(device)


def _bytes(data) -> int | None:
    try:
        if hasattr(data, "nbytes"):
            return int(data.nbytes)
        return int(data.numel() * data.element_size())
    except Exception:
        return None


def _caller() -> str:
    """First frame outside arraybridge and this module: who asked for the conversion."""
    frame = sys._getframe(2)
    while frame is not None:
        filename = frame.f_code.co_filename
        if "arraybridge" not in filename and not filename.endswith("conversion_trace.py"):
            parts = filename.replace("\\", "/").split("/")
            return f"{'/'.join(parts[-2:])}:{frame.f_lineno} {frame.f_code.co_name}"
        frame = frame.f_back
    return "unknown"


def _write(record: dict) -> None:
    path = os.environ.get("OPENHCS_CONVERSION_TRACE")
    if not path:
        return
    record["pid"] = os.getpid()
    with _LOCK, open(path, "a", encoding="utf-8") as handle:
        handle.write(json.dumps(record) + "\n")


def install() -> None:
    """Wrap the conversion methods once per process."""
    if getattr(MemoryType, "_conversion_trace_installed", False):
        return
    convert_to = MemoryType.convert_to
    from_dlpack = MemoryType.from_dlpack
    to_numpy = MemoryType.to_numpy
    from_numpy = MemoryType.from_numpy

    def traced_convert_to(self, data, target, device_id):
        outer = getattr(_STATE, "route", None)
        _STATE.route = [] if self is not target else ["same"]
        started = time.perf_counter()
        try:
            result = convert_to(self, data, target, device_id)
        finally:
            route = _STATE.route
            _STATE.route = outer
        source_address = _buffer_address(data)
        result_address = _buffer_address(result)
        _write(
            {
                "event": "convert",
                "source": self.value,
                "target": target.value,
                "source_device": _device(data),
                "target_device": _device(result),
                "shape": list(getattr(data, "shape", ())),
                "dtype": str(getattr(data, "dtype", "")),
                "bytes": _bytes(data),
                "route": "host" if "host" in route else (route[-1] if route else "unknown"),
                "shares_buffer": source_address is not None and source_address == result_address,
                "seconds": round(time.perf_counter() - started, 6),
                "caller": _caller(),
            }
        )
        return result

    def traced_from_dlpack(self, data, module=None):
        result = from_dlpack(self, data, module)
        route = getattr(_STATE, "route", None)
        if route is not None and result is not NotImplemented:
            route.append("dlpack")
        return result

    def traced_to_numpy(self, data, module=None):
        route = getattr(_STATE, "route", None)
        if route is not None:
            route.append("host")
            return to_numpy(self, data, module)
        started = time.perf_counter()
        result = to_numpy(self, data, module)
        if self.value != "numpy":
            _write(
                {
                    "event": "to_host",
                    "source": self.value,
                    "source_device": _device(data),
                    "shape": list(getattr(data, "shape", ())),
                    "bytes": _bytes(data),
                    "seconds": round(time.perf_counter() - started, 6),
                    "caller": _caller(),
                }
            )
        return result

    def traced_from_numpy(self, data, device_id, *args, **kwargs):
        route = getattr(_STATE, "route", None)
        if route is not None:
            route.append("host")
            return from_numpy(self, data, device_id, *args, **kwargs)
        started = time.perf_counter()
        result = from_numpy(self, data, device_id, *args, **kwargs)
        if self.value != "numpy":
            _write(
                {
                    "event": "from_host",
                    "target": self.value,
                    "target_device": _device(result),
                    "shape": list(getattr(data, "shape", ())),
                    "bytes": _bytes(data),
                    "seconds": round(time.perf_counter() - started, 6),
                    "caller": _caller(),
                }
            )
        return result

    MemoryType.convert_to = traced_convert_to
    MemoryType.from_dlpack = traced_from_dlpack
    MemoryType.to_numpy = traced_to_numpy
    MemoryType.from_numpy = traced_from_numpy
    MemoryType._conversion_trace_installed = True


def summarise(path: str) -> list[dict]:
    """Group a trace file by (event, source, target, devices, route)."""
    groups: dict[tuple, dict] = {}
    with open(path, encoding="utf-8") as handle:
        for line in handle:
            record = json.loads(line)
            key = (
                record["event"],
                record.get("source", "numpy"),
                record.get("target", "numpy"),
                record.get("source_device", "cpu"),
                record.get("target_device", "cpu"),
                record.get("route", "host"),
                record.get("shares_buffer", False),
                record.get("caller", ""),
            )
            group = groups.setdefault(key, {"count": 0, "bytes": 0, "seconds": 0.0})
            group["count"] += 1
            group["bytes"] += record.get("bytes") or 0
            group["seconds"] += record.get("seconds", 0.0)
    return [
        {
            "event": key[0],
            "source": f"{key[1]} ({key[3]})",
            "target": f"{key[2]} ({key[4]})",
            "route": key[5],
            "shares_buffer": key[6],
            "requested_by": key[7],
            "count": group["count"],
            "megabytes": round(group["bytes"] / 1e6, 2),
            "seconds": round(group["seconds"], 4),
        }
        for key, group in sorted(groups.items())
    ]
