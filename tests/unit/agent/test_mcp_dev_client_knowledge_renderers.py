"""Knowledge, function and ObjectState renderers over typed DTO fixtures."""

from __future__ import annotations

import ast
from pathlib import Path

import pytest

from openhcs.agent.dto.architecture import (
    ArchitectureTopic,
    ArchitectureTopicPage,
    ArchitectureTopicSummary,
    InternalApiSymbol,
)
from openhcs.agent.dto.authoring import AuthoringContext
from openhcs.agent.dto.common import SCHEMA_VERSION, AgentError, AgentWarning
from openhcs.agent.dto.functions import (
    FunctionArtifactSpec,
    FunctionCatalogEntry,
    FunctionCatalogPage,
    FunctionDetail,
    FunctionParameterSource,
    FunctionParameterSpec,
    FunctionRuntimeContractSummary,
)
from openhcs.agent.dto.knowledge import (
    KnowledgeBaseCatalog,
    KnowledgeBaseDocument,
    KnowledgeBaseDocumentSummary,
    KnowledgeBaseSearchHit,
    KnowledgeBaseSearchResult,
    KnowledgeBaseSectionSummary,
    KnowledgeBaseSourceSpan,
)
from openhcs.agent.dto.ui_bridge import (
    UiCatalogPageMetadata,
    UiMutationReceipt,
    UiMutationRequestToken,
    UiObjectStateFieldHelpResult,
    UiObjectStateFieldListResult,
    UiObjectStateFieldMutationResult,
    UiObjectStateFieldProjection,
    UiObjectStateFieldProvenance,
    UiObjectStateFieldScopeProjection,
    UiObjectStateFieldSummary,
    UiObjectStateScopeCatalog,
    UiObjectStateScopeIdentity,
    UiObjectStateScopeSummary,
    UiObjectStateValuePreview,
    UiSemanticAddress,
)
from openhcs.mcp.dev_client_core import (
    McpDevServerIdentity,
    McpDevToolBatchResponse,
    McpDevToolResult,
)
from openhcs.mcp.dev_client_renderers import knowledge, object_state
from openhcs.mcp.dev_client_rendering import (
    AuthoringContextRenderOptions,
    CatalogRenderOptions,
    McpDevOutputRenderer,
)


def _batch(*payloads, tool="openhcs_any_tool") -> McpDevToolBatchResponse:
    return McpDevToolBatchResponse(
        server=McpDevServerIdentity(command="python", module="openhcs.mcp"),
        results=(McpDevToolResult(tool=tool, mcp_error=False, payloads=payloads),),
    )


def _render(payload, options=None) -> str:
    renderer = McpDevOutputRenderer.for_output_contract(type(payload))
    assert renderer is not None, type(payload)
    return renderer.render(_batch(payload), options)


def _document(index: int, tags=("alpha",)) -> KnowledgeBaseDocumentSummary:
    return KnowledgeBaseDocumentSummary(
        document_id=f"doc-{index}",
        title=f"Document {index}",
        summary="About things.",
        source_path=f"docs/{index}.md",
        tags=tags,
        section_count=2,
    )


def _section(section_id: str, title: str) -> KnowledgeBaseSectionSummary:
    return KnowledgeBaseSectionSummary(
        section_id, title, 2, KnowledgeBaseSourceSpan(1, 3)
    )


def _entry(function_id: str = "openhcs:count") -> FunctionCatalogEntry:
    return FunctionCatalogEntry(
        function_id=function_id,
        import_path="openhcs.processing.count",
        name="count",
        module="openhcs.processing",
        library="openhcs",
        signature="count(image, threshold)",
        summary="Count objects.",
        backend_tags=("numpy", "cupy"),
    )


def _field_summary(path: str, **semantics) -> UiObjectStateFieldSummary:
    return UiObjectStateFieldSummary(
        schema_version=SCHEMA_VERSION,
        address=UiSemanticAddress(object_state_scope_id="scope-1", field_path=path),
        field_name=path.rsplit(".", 1)[-1],
        container_path="",
        object_state_path_type="openhcs.config.PipelineConfig",
        raw_value_type="int",
        resolved_value_type="int",
        **semantics,
    )


SCOPE_CATALOG = UiObjectStateScopeCatalog(
    schema_version=SCHEMA_VERSION,
    object_state_token=7,
    current_branch="main",
    current_snapshot_index=3,
    scopes=(
        UiObjectStateScopeSummary(
            schema_version=SCHEMA_VERSION,
            identity=UiObjectStateScopeIdentity(object_state_scope_id="scope-1"),
            object_type="PipelineConfig",
            parameter_count=4,
            dirty_field_count=1,
            signature_diff_field_count=0,
            field_page=UiCatalogPageMetadata(
                limit=1, returned_count=1, total_count=4, next_offset=1
            ),
            fields=(
                _field_summary(
                    "num_workers",
                    dirty=True,
                    raw_value_preview=UiObjectStateValuePreview("int", False, "4"),
                    resolved_value_preview=UiObjectStateValuePreview("int", False, "4"),
                ),
            ),
        ),
    ),
)

FIELD_LIST = UiObjectStateFieldListResult(
    schema_version=SCHEMA_VERSION,
    object_state_token=7,
    current_branch="main",
    current_snapshot_index=3,
    requested_scope_ids=("scope-1",),
    field_paths=(),
    field_path_contains=("worker",),
    field_filter="dirty",
    include_container_fields=False,
    matched_scope_count=1,
    matched_field_count=2,
    returned_field_count=2,
    field_limit=200,
    field_offset=0,
    next_offset=None,
    truncated=False,
    scopes=(
        UiObjectStateFieldScopeProjection(
            scope_id="scope-1",
            object_type="PipelineConfig",
            dirty_field_count=1,
            signature_diff_field_count=1,
            has_unsaved_changes=True,
            has_default_overrides=False,
            fields=(
                UiObjectStateFieldProjection(
                    field_path="num_workers",
                    field_name="num_workers",
                    container_path="",
                    object_state_path_type="openhcs.config.PipelineConfig",
                    raw_value_type="int",
                    resolved_value_type="int",
                    dirty=True,
                    raw_value=4,
                    resolved_value=4,
                ),
                UiObjectStateFieldProjection(
                    field_path="worker_mode",
                    field_name="worker_mode",
                    container_path="",
                    object_state_path_type="openhcs.config.PipelineConfig",
                    raw_value_type="NoneType",
                    resolved_value_type="str",
                    raw_value_is_none=True,
                    inherited_value=True,
                    resolved_value="process",
                    provenance=UiObjectStateFieldProvenance(
                        "global", "openhcs.config.GlobalConfig", "worker_mode"
                    ),
                ),
            ),
        ),
    ),
)

# One typed instance per registered renderer in these modules, with the lines
# each presentation must contain.
FAMILY_CASES = (
    (
        KnowledgeBaseCatalog(
            schema_version=SCHEMA_VERSION,
            documents=(_document(1), _document(2, tags=tuple("abcdefgh"))),
        ),
        ("Knowledge documents: matched=2 shown=2", "tags=a,b,c,d,e,f,+2"),
    ),
    (
        KnowledgeBaseSearchResult(
            schema_version=SCHEMA_VERSION,
            query="cells",
            hits=(
                KnowledgeBaseSearchHit(
                    _document(1), _section("intro", "Intro"), 4, "count cells", 3,
                    ("cells",),
                ),
            ),
        ),
        ('query="cells" hits=1', "- doc-1#intro: score=3 line=4", "  count cells"),
    ),
    (
        KnowledgeBaseDocument(
            schema_version=SCHEMA_VERSION,
            document=_document(1),
            sections=(_section("intro", "Intro"), _section("usage", "usage")),
            content="Body text",
            truncated=True,
        ),
        ("Sections:", "- intro: Intro", "- usage", "Body text", "Content truncated"),
    ),
    (
        ArchitectureTopicPage(
            SCHEMA_VERSION, (ArchitectureTopicSummary("compiler", "Compiler", "Plans."),)
        ),
        ('- compiler: title="Compiler" summary="Plans."',),
    ),
    (
        ArchitectureTopic(
            SCHEMA_VERSION, "compiler", "Compiler", "Plans.", ("axes",), ("CP note",),
            (
                InternalApiSymbol(
                    "openhcs.core.Compiler", "compiler", "Compiler", "plans", "class",
                    None, None, "openhcs/core/compiler.py", 10,
                ),
            ),
        ),
        ("Summary: Plans.", "- axes", "- CP note", "source=openhcs/core/compiler.py:10", "  role=plans"),
    ),
    (
        InternalApiSymbol(
            "openhcs.core.Compiler", "compiler", "Compiler", "plans", "class",
            "Compiler()", "Compiles.", None, None,
        ),
        ("Source: <none>", "Signature: Compiler()", "Role: plans", "Doc: Compiles."),
    ),
    (
        FunctionCatalogPage(SCHEMA_VERSION, "rev", (_entry(),), total=9, limit=1, query="count"),
        ('query="count" library=<none> shown=1 total=9', "tags=numpy,cupy", "  Count objects."),
    ),
    (
        FunctionDetail(
            SCHEMA_VERSION,
            _entry(),
            (
                FunctionParameterSpec("threshold", "float", "0.5", False),
                FunctionParameterSpec(
                    "image", "ndarray", None, True,
                    supplied_by=FunctionParameterSource.PRIMARY_INPUT,
                    description="From the step input.",
                ),
            ),
            "Long doc",
            runtime_contract=FunctionRuntimeContractSummary(
                "function", artifact_outputs=(FunctionArtifactSpec("labels", "label_image"),)
            ),
            doc_truncated=True,
            doc_chars=8,
        ),
        (
            "Agent parameters:",
            "- threshold: required=False type=float default=0.5",
            '- image: supplied_by=runtime_primary_input type=ndarray note="From the step input."',
            "- labels: kind=label_image required=True",
            "Doc truncated; rerun: function openhcs:count --max-doc-chars 8",
        ),
    ),
    (
        AuthoringContext(
            SCHEMA_VERSION,
            "first_use",
            "x" * (AuthoringContextRenderOptions().max_chars + 5),
        ),
        ("Authoring context: kind=first_use", "<truncated 5 chars>"),
    ),
    (
        SCOPE_CATALOG,
        (
            "ObjectState scopes: scopes=1 token=7 branch=main snapshot=3 active=False",
            "- [*] scope=scope-1: type=PipelineConfig params=4 dirty=1 default_diff=0",
            "fields=1/4 next=1",
            "  [*] num_workers: target=PipelineConfig raw=4 -> resolved=4",
            "Next field page: rerun with --include-fields --field-offset 1 --field-limit 1",
        ),
    ),
    (
        FIELD_LIST,
        (
            "returned=2 offset=0 limit=200 truncated=False",
            "Returned semantics: dirty=1 default_diff=0 inherited=1 raw_none_resolved=1 resolved_none_raw=0 plain=0",
            "Filters: scope_ids=scope-1 contains=worker field_filter=dirty",
            "Scope [*_] scope=scope-1:",
            "provenance=global:worker_mode (GlobalConfig)",
        ),
    ),
    (
        UiObjectStateFieldHelpResult(
            schema_version=SCHEMA_VERSION,
            address=UiSemanticAddress("scope-1", "num_workers"),
            field=_field_summary("num_workers"),
            object_type="openhcs.config.PipelineConfig",
            target_summary="  Worker   count. " * 30,
            description="Number of workers.",
            description_truncated=True,
        ),
        ("scope=scope-1 field=num_workers", "object=PipelineConfig", "Field:", "...", "Description truncated"),
    ),
    (
        UiObjectStateFieldMutationResult(
            schema_version=SCHEMA_VERSION,
            address=UiSemanticAddress("scope-1", "num_workers"),
            mutated=True,
            reset=False,
            receipt=UiMutationReceipt(UiMutationRequestToken("t"), "op-1", True),
            before=_field_summary("num_workers"),
            after=_field_summary("num_workers", dirty=True),
        ),
        ("mutated=True reset=False", "accepted=True operation=op-1", "Before:", "After:", "  [*] num_workers"),
    ),
)


@pytest.mark.parametrize("payload, expected", FAMILY_CASES, ids=lambda value: type(value).__name__)
def test_each_renderer_presents_its_declared_dto(payload, expected) -> None:
    rendered = _render(payload)
    for line in expected:
        assert line in rendered


def test_every_renderer_in_these_modules_has_a_family_case() -> None:
    covered = {type(payload) for payload, _ in FAMILY_CASES}
    declared = {
        renderer.output_contract
        for module in (knowledge, object_state)
        for renderer in vars(module).values()
        if isinstance(renderer, type)
        and issubclass(renderer, McpDevOutputRenderer)
        and vars(renderer).get("output_contract") is not None
    }
    # Custom-function registration has its own journey tests.
    declared.discard(knowledge.CustomFunctionRegistrationRenderer.output_contract)
    assert declared == covered


def test_catalog_filters_and_truncation_are_declared_options() -> None:
    catalog = KnowledgeBaseCatalog(
        schema_version=SCHEMA_VERSION,
        documents=(_document(1, tags=("beta",)), _document(2), _document(3)),
    )
    rendered = _render(catalog, CatalogRenderOptions(contains="alpha", limit=1))
    assert "Knowledge documents: matched=2 shown=1" in rendered
    assert "Filter: contains=alpha" in rendered
    assert "...<truncated 1 documents>" in rendered
    assert "doc-1" not in rendered

    topics = ArchitectureTopicPage(
        SCHEMA_VERSION,
        tuple(ArchitectureTopicSummary(f"t{i}", f"T{i}", "s") for i in range(3)),
    )
    assert "...<truncated 2 topics>" in _render(topics, CatalogRenderOptions(limit=1))
    assert (
        _render(AuthoringContext(SCHEMA_VERSION, "k", "abc"), AuthoringContextRenderOptions(max_chars=1))
        .endswith("a\n...<truncated 2 chars>")
    )


def test_payload_warnings_and_errors_are_rendered_once_by_the_base() -> None:
    catalog = KnowledgeBaseCatalog(
        schema_version=SCHEMA_VERSION,
        documents=(),
        warnings=(AgentWarning("partial", "Some docs skipped."),),
        errors=(AgentError("index_stale", "Index is stale.", "Rebuild."),),
    )
    rendered = _render(catalog)
    assert rendered.count("partial: Some docs skipped.") == 1
    assert rendered.count('index_stale: Index is stale. hint="Rebuild."') == 1
    assert rendered.index("Warnings:") < rendered.index("Errors:")


def test_missing_payload_renders_the_declared_unavailable_line() -> None:
    response = McpDevToolBatchResponse(
        server=McpDevServerIdentity(command="python", module="openhcs.mcp"),
        results=(McpDevToolResult(tool="openhcs_list_knowledge_documents", mcp_error=True, payloads=()),),
    )
    rendered = knowledge.KnowledgeCatalogRenderer.render(response)
    assert rendered.startswith("Knowledge documents: unavailable\nErrors:\n")


def test_renderer_modules_read_no_mappings() -> None:
    for module in (knowledge, object_state):
        tree = ast.parse(Path(module.__file__).read_text())
        assert not any(
            isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr == "get"
            for node in ast.walk(tree)
        ), module.__name__
