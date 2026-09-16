#!/usr/bin/env python
"""Compatibility wrapper for the installed OpenHCS benchmark CLI."""

from benchmark.cellprofiler_benchmark_cli import main

if __name__ == "__main__":
    raise SystemExit(main())
