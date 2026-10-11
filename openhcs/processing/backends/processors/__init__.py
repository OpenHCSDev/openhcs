"""
Image processors for the array backends (numpy, cupy, torch, tensorflow, jax,
pyclesperanto).

Operations shared by several backends are written once in
``image_stack_operations`` against arraybridge ``ArrayOperations``; each
``<backend>_processor`` module registers them for its memory type and keeps
only the operations whose algorithm differs on that backend.
"""
