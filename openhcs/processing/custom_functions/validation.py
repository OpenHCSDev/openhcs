"""
Code validation utilities for custom functions.

Provides validation before exec() to catch common errors early and provide
helpful error messages. Follows OpenHCS fail-loud principle: invalid code
should fail immediately with clear diagnostics.

Security note: This module provides basic validation but does not sandbox
exec(). Custom functions execute with full Python privileges.
"""

import ast
import inspect
from dataclasses import dataclass, replace
from typing import Callable

from openhcs.core.callable_contract import FunctionStepExecutionScope


class ValidationError(Exception):
    """
    Exception raised when custom function code is invalid.

    Attributes:
        message: Human-readable error description
        line_number: Optional line number where error occurred
        code_snippet: Optional code snippet showing the error
    """

    def __init__(self, message: str, line_number: int = 0, code_snippet: str = ""):
        self.message = message
        self.line_number = line_number
        self.code_snippet = code_snippet
        super().__init__(self._format_message())

    def _format_message(self) -> str:
        """Format error message with line number and code snippet if available."""
        parts = [self.message]
        if self.line_number > 0:
            parts.append(f"Line {self.line_number}")
        if self.code_snippet:
            parts.append(f"Code: {self.code_snippet}")
        return " | ".join(parts)


@dataclass(frozen=True)
class ValidationResult:
    """
    Result of code validation.

    Attributes:
        is_valid: Whether the code passed validation
        errors: List of validation error messages
        warnings: List of non-fatal warning messages
        function_names: List of function names found in the code
    """

    is_valid: bool
    errors: list[str]
    warnings: list[str]
    function_names: list[str]


def validate_syntax(code: str) -> ValidationResult:
    """
    Validate Python syntax using ast.parse.

    Args:
        code: Python code string to validate

    Returns:
        ValidationResult with syntax validation results
    """
    try:
        tree = ast.parse(code)
        return ValidationResult(
            is_valid=True,
            errors=[],
            warnings=[],
            function_names=[
                declaration.name
                for declaration in tree.body
                if isinstance(declaration, ast.FunctionDef)
            ],
        )
    except SyntaxError as e:
        error_msg = f"Syntax error: {e.msg}"
        return ValidationResult(
            is_valid=False, errors=[error_msg], warnings=[], function_names=[]
        )


def validate_imports(code: str) -> ValidationResult:
    """
    Validate that code doesn't import dangerous modules.

    Args:
        code: Python code string to validate

    Returns:
        ValidationResult with import validation results
    """
    # Modules that should not be imported in custom functions
    dangerous_modules: set[str] = {
        "os",
        "sys",
        "subprocess",
        "shutil",
        "glob",
        "socket",
        "urllib",
        "requests",
        "http",
        "eval",
        "exec",
        "compile",
        "__import__",
    }

    errors: list[str] = []
    warnings: list[str] = []

    try:
        tree = ast.parse(code)
    except SyntaxError:
        # Syntax errors will be caught by validate_syntax
        return ValidationResult(
            is_valid=True, errors=[], warnings=[], function_names=[]
        )

    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                module_name = alias.name.split(".")[0]
                if module_name in dangerous_modules:
                    errors.append(
                        f"Dangerous import detected: '{alias.name}'. "
                        f"Module '{module_name}' is not allowed in custom functions."
                    )

        elif isinstance(node, ast.ImportFrom):
            if node.module:
                module_name = node.module.split(".")[0]
                if module_name in dangerous_modules:
                    errors.append(
                        f"Dangerous import detected: 'from {node.module}'. "
                        f"Module '{module_name}' is not allowed in custom functions."
                    )

    is_valid = len(errors) == 0
    return ValidationResult(
        is_valid=is_valid, errors=errors, warnings=warnings, function_names=[]
    )


def validate_code(code: str) -> ValidationResult:
    """
    Run all code validations before exec().

    Performs syntax and import validation and identifies source declarations.
    Memory and processing semantics are checked on the executed callable by
    CustomFunctionManager, not inferred from decorator names or syntax.

    Args:
        code: Python code string to validate

    Returns:
        ValidationResult with combined validation results
    """
    # Validate syntax first
    syntax_result = validate_syntax(code)
    if not syntax_result.is_valid:
        return syntax_result

    # Validate imports
    result = validate_imports(code)
    if not result.is_valid:
        return result

    return replace(result, function_names=syntax_result.function_names)


def validate_function(func: Callable) -> ValidationResult:
    """Validate the selected declaration using its original scope contract."""
    from openhcs.processing.backends.lib_registry.openhcs_registry import OpenHCSRegistry

    errors: list[str] = []
    try:
        contract = OpenHCSRegistry.declared_callable_contract(func)
        if contract is None:
            raise ValueError(f"Function {func.__name__!r} is not an admitted OpenHCS declaration.")
        if contract.execution_scope is FunctionStepExecutionScope.PLATE:
            from openhcs.core.pipeline.funcstep_contract_validator import FuncStepContractValidator

            FuncStepContractValidator.validate_plate_callable_contracts(
                (contract,), func.__name__,
            )
        else:
            params = tuple(inspect.signature(func).parameters)
            if not params or params[0] != "image":
                raise ValueError(
                    f"Function {func.__name__!r} first parameter must be 'image'."
                )
    except (TypeError, ValueError) as exc:
        errors.append(str(exc))
    return ValidationResult(
        is_valid=not errors, errors=errors, warnings=[], function_names=[func.__name__],
    )
