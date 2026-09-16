"""Headless OpenHCS agent-service package.

Consumers import each nominal service from its declaring module. Keeping package
initialization empty prevents unrelated execution processes from importing the
entire agent capability and service graph.
"""
