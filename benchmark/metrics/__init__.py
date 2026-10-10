"""Metric collectors."""

from python_introspect import public_names_from_objects

from benchmark.metrics.time import TimeMetric
from benchmark.metrics.memory import MemoryMetric

__all__ = public_names_from_objects(TimeMetric, MemoryMetric)
