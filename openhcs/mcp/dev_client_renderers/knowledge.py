"""Knowledge, architecture, and function renderers for the MCP dev client."""

from __future__ import annotations

from typing import ClassVar

from openhcs.agent.dto.architecture import (
    ArchitectureTopic,
    ArchitectureTopicPage,
    ArchitectureTopicSummary,
    InternalApiSymbol,
)
from openhcs.agent.dto.authoring import AuthoringContext
from openhcs.agent.dto.functions import (
    CustomFunctionRegistrationResult,
    FunctionArtifactSpec,
    FunctionCatalogEntry,
    FunctionCatalogPage,
    FunctionDetail,
    FunctionParameterSource,
    FunctionParameterSpec,
)
from openhcs.agent.dto.knowledge import (
    KnowledgeBaseCatalog,
    KnowledgeBaseDocument,
    KnowledgeBaseDocumentSummary,
    KnowledgeBaseSearchHit,
    KnowledgeBaseSearchResult,
    KnowledgeBaseSectionSummary,
)
from openhcs.mcp.dev_client_rendering import (
    AuthoringContextRenderOptions,
    CatalogRenderOptions,
    CodeDocumentRenderOptions,
    McpDevOutputRenderer,
    McpDevOutputRenderOptions,
)


class KnowledgeCatalogRenderer(McpDevOutputRenderer):
    """Compact renderer for knowledge-base document catalogs."""

    output_contract = KnowledgeBaseCatalog
    render_options_type = CatalogRenderOptions
    unavailable_summary = "Knowledge documents: unavailable"

    @classmethod
    def render_payload(
        cls, payload: KnowledgeBaseCatalog, options: CatalogRenderOptions
    ) -> str:
        documents, visible_documents = options.select(
            payload.documents,
            lambda document: " ".join(
                (document.document_id, document.title, document.summary, *document.tags)
            ),
        )
        lines = [
            "Knowledge documents: "
            f"matched={len(documents)} shown={len(visible_documents)}",
            *options.filter_lines(),
        ]
        if visible_documents:
            lines.append("Documents:")
            lines.extend(cls._document_line(document) for document in visible_documents)
        if len(visible_documents) < len(documents):
            lines.append(
                f"...<truncated {len(documents) - len(visible_documents)} documents>"
            )
        return "\n".join(lines)

    @classmethod
    def _document_line(cls, document: KnowledgeBaseDocumentSummary) -> str:
        tag_text = ",".join(document.tags[:6])
        if len(document.tags) > 6:
            tag_text += f",+{len(document.tags) - 6}"
        return (
            f"- {document.document_id}: title={cls.quoted(document.title)} "
            f"sections={document.section_count} path={document.source_path} "
            f"tags={tag_text}"
        )


class KnowledgeSearchRenderer(McpDevOutputRenderer):
    """Compact renderer for knowledge search hits."""

    output_contract = KnowledgeBaseSearchResult
    unavailable_summary = "Knowledge search: unavailable"

    @classmethod
    def render_payload(
        cls, payload: KnowledgeBaseSearchResult, options: McpDevOutputRenderOptions
    ) -> str:
        lines = [
            f"Knowledge search: query={cls.quoted(payload.query)} "
            f"hits={len(payload.hits)}"
        ]
        if payload.hits:
            lines.append("Hits:")
            for hit in payload.hits:
                lines.extend(cls._hit_lines(hit))
        return "\n".join(lines)

    @classmethod
    def _hit_lines(cls, hit: KnowledgeBaseSearchHit) -> list[str]:
        section = hit.section
        lines = [
            f"- {hit.document.document_id}"
            f"#{cls.text(None if section is None else section.section_id)}: "
            f"score={hit.score} line={cls.text(hit.line_number)} "
            f"title={cls.quoted(None if section is None else section.title)} "
            f"terms={cls.sequence_text(hit.matched_terms)}"
        ]
        if hit.snippet:
            lines.append(f"  {hit.snippet}")
        return lines


class KnowledgeDocumentRenderer(McpDevOutputRenderer):
    """Compact renderer for one knowledge-base document or section."""

    output_contract = KnowledgeBaseDocument
    unavailable_summary = "Knowledge document: unavailable"

    MAX_SECTION_HINTS: ClassVar[int] = 12

    @classmethod
    def render_payload(
        cls, payload: KnowledgeBaseDocument, options: McpDevOutputRenderOptions
    ) -> str:
        document = payload.document
        lines = [
            "Knowledge document: "
            f"id={cls.text(None if document is None else document.document_id)} "
            f"title={cls.quoted(None if document is None else document.title)} "
            f"path={cls.text(None if document is None else document.source_path)} "
            f"sections={len(payload.sections)} max_chars={payload.max_chars}"
        ]
        if payload.selected_section_id is not None:
            lines.append(f"Selected section: {payload.selected_section_id}")
        elif payload.sections:
            lines.extend(cls._section_hint_lines(payload.sections))
        lines.append("Content:")
        lines.append(payload.content)
        if payload.truncated:
            lines.append(
                "Content truncated; rerun with a larger --max-chars or a narrower "
                "--section-id."
            )
        return "\n".join(lines)

    @classmethod
    def _section_hint_lines(
        cls,
        sections: tuple[KnowledgeBaseSectionSummary, ...],
    ) -> list[str]:
        lines = ["Sections:"]
        visible_sections = sections[: cls.MAX_SECTION_HINTS]
        for section in visible_sections:
            if section.title and section.title != section.section_id:
                lines.append(f"- {section.section_id}: {section.title}")
            else:
                lines.append(f"- {section.section_id}")
        omitted_count = len(sections) - len(visible_sections)
        if omitted_count > 0:
            lines.append(f"- ... {omitted_count} more sections")
        return lines


class ArchitectureCatalogRenderer(McpDevOutputRenderer):
    """Compact renderer for architecture topic catalogs."""

    output_contract = ArchitectureTopicPage
    render_options_type = CatalogRenderOptions
    unavailable_summary = "Architecture topics: unavailable"

    @classmethod
    def render_payload(
        cls, payload: ArchitectureTopicPage, options: CatalogRenderOptions
    ) -> str:
        topics, visible_topics = options.select(
            payload.topics,
            lambda topic: " ".join((topic.topic_id, topic.title, topic.summary)),
        )
        lines = [
            f"Architecture topics: matched={len(topics)} shown={len(visible_topics)}",
            *options.filter_lines(),
        ]
        if visible_topics:
            lines.append("Topics:")
            lines.extend(cls._topic_line(topic) for topic in visible_topics)
        if len(visible_topics) < len(topics):
            lines.append(f"...<truncated {len(topics) - len(visible_topics)} topics>")
        return "\n".join(lines)

    @classmethod
    def _topic_line(cls, topic: ArchitectureTopicSummary) -> str:
        return (
            f"- {topic.topic_id}: title={cls.quoted(topic.title)} "
            f"summary={cls.quoted(topic.summary)}"
        )


class InternalSymbolPresentation(McpDevOutputRenderer):
    """Source location text shared by symbol presentations."""

    @classmethod
    def source_text(cls, symbol: InternalApiSymbol) -> str:
        source = cls.text(symbol.source_path)
        if symbol.line_number is None:
            return source
        return f"{source}:{symbol.line_number}"


class ArchitectureTopicRenderer(InternalSymbolPresentation):
    """Compact renderer for one source-backed architecture topic."""

    output_contract = ArchitectureTopic
    unavailable_summary = "Architecture topic: unavailable"

    @classmethod
    def render_payload(
        cls, payload: ArchitectureTopic, options: McpDevOutputRenderOptions
    ) -> str:
        lines = [
            "Architecture topic: "
            f"id={payload.topic_id} title={cls.quoted(payload.title)} "
            f"concepts={len(payload.concepts)} "
            f"symbols={len(payload.internal_symbols)}"
        ]
        if payload.summary:
            lines.append(f"Summary: {payload.summary}")
        if payload.concepts:
            lines.append("Concepts:")
            lines.extend(f"- {concept}" for concept in payload.concepts)
        if payload.cellprofiler_translation_notes:
            lines.append("CellProfiler notes:")
            lines.extend(f"- {note}" for note in payload.cellprofiler_translation_notes)
        if payload.internal_symbols:
            lines.append("Internal symbols:")
            for symbol in payload.internal_symbols:
                lines.append(
                    f"- {symbol.symbol_id}: {symbol.title} "
                    f"kind={symbol.symbol_kind} import={symbol.import_path} "
                    f"source={cls.source_text(symbol)}"
                )
                if symbol.role:
                    lines.append(f"  role={symbol.role}")
        return "\n".join(lines)


class InternalSymbolRenderer(InternalSymbolPresentation):
    """Compact renderer for one internal architecture symbol."""

    output_contract = InternalApiSymbol
    unavailable_summary = "Internal symbol: unavailable"

    @classmethod
    def render_payload(
        cls, payload: InternalApiSymbol, options: McpDevOutputRenderOptions
    ) -> str:
        lines = [
            "Internal symbol: "
            f"id={payload.symbol_id} title={cls.quoted(payload.title)} "
            f"kind={payload.symbol_kind}",
            f"Import: {payload.import_path}",
            f"Source: {cls.source_text(payload)}",
        ]
        if payload.signature:
            lines.append(f"Signature: {payload.signature}")
        if payload.role:
            lines.append(f"Role: {payload.role}")
        if payload.doc_summary is not None:
            lines.append(f"Doc: {payload.doc_summary}")
        return "\n".join(lines)


class FunctionEntryPresentation(McpDevOutputRenderer):
    """Catalog-entry lines shared by function search and registration."""

    @classmethod
    def entry_lines(cls, entry: FunctionCatalogEntry) -> list[str]:
        lines = [
            f"- {entry.function_id}: {entry.signature} "
            f"tags={cls.sequence_text(entry.backend_tags)}"
        ]
        if entry.summary:
            lines.append(f"  {entry.summary}")
        return lines


class FunctionSearchRenderer(FunctionEntryPresentation):
    """Compact renderer for processing-function search results."""

    output_contract = FunctionCatalogPage
    unavailable_summary = "Function search: unavailable"

    @classmethod
    def render_payload(
        cls, payload: FunctionCatalogPage, options: McpDevOutputRenderOptions
    ) -> str:
        lines = [
            "Function search: "
            f"query={cls.quoted(payload.query)} library={cls.text(payload.library)} "
            f"shown={len(payload.items)} total={payload.total}"
        ]
        if payload.items:
            lines.append("Functions:")
            for item in payload.items:
                lines.extend(cls.entry_lines(item))
        return "\n".join(lines)


class CustomFunctionRegistrationRenderer(FunctionEntryPresentation):
    """Compact renderer for custom-function registration results."""

    output_contract = CustomFunctionRegistrationResult
    unavailable_summary = "Custom function registration: <unavailable>"

    @classmethod
    def render_payload(
        cls,
        payload: CustomFunctionRegistrationResult,
        options: McpDevOutputRenderOptions,
    ) -> str:
        if payload.errors:
            return "\n".join(
                (
                    "Custom function registration: incomplete observation",
                    f"Reported registered_count: {payload.registered_count} "
                    "(zero/absent does not prove no mutation)",
                    "Read-only observation handle: "
                    + cls.json_text(payload.observation_handle),
                )
            )
        lines = [
            "Custom function registration: "
            f"registered={payload.registered_count} "
            f"persisted={payload.persisted} storage={cls.text(payload.storage_dir)}"
        ]
        if payload.source_file_paths:
            lines.append(f"Files: {','.join(payload.source_file_paths)}")
        if payload.functions:
            lines.append("Functions:")
            for function in payload.functions:
                lines.extend(cls.entry_lines(function))
            if payload.persisted is False:
                lines.append(
                    "Lifetime: process-local only; follow-up dev_client commands "
                    "start a fresh MCP process. Omit --no-persist or reuse the "
                    "same MCP session before using these function ids."
                )
            lines.append("Next:")
            for function in payload.functions:
                lines.append(f"- function {function.function_id}")
                lines.append(
                    f"- draft-pipeline-step {function.function_id} --name <step_name>"
                )
        return "\n".join(lines)


class FunctionDetailRenderer(McpDevOutputRenderer):
    """Compact renderer for one processing-function detail payload."""

    output_contract = FunctionDetail
    unavailable_summary = "Function: unavailable"

    @classmethod
    def render_payload(
        cls, payload: FunctionDetail, options: McpDevOutputRenderOptions
    ) -> str:
        entry = payload.entry
        agent_parameters = tuple(
            parameter
            for parameter in payload.parameters
            if parameter.supplied_by is FunctionParameterSource.AGENT
        )
        runtime_parameters = tuple(
            parameter
            for parameter in payload.parameters
            if parameter.supplied_by is not FunctionParameterSource.AGENT
        )
        artifact_outputs = (
            ()
            if payload.runtime_contract is None
            else payload.runtime_contract.artifact_outputs
        )
        lines = [
            f"Function: id={entry.function_id} name={entry.name} library={entry.library}",
            f"Signature: {entry.signature}",
        ]
        if entry.summary:
            lines.append(f"Summary: {entry.summary}")
        if agent_parameters:
            lines.append("Agent parameters:")
            lines.extend(cls._parameter_line(parameter) for parameter in agent_parameters)
        if runtime_parameters:
            lines.append("Runtime inputs:")
            lines.extend(
                cls._runtime_parameter_line(parameter) for parameter in runtime_parameters
            )
        if artifact_outputs:
            lines.append("Artifact outputs:")
            lines.extend(cls._artifact_line(artifact) for artifact in artifact_outputs)
        if payload.doc:
            lines.append(
                f"Doc: chars={payload.doc_chars} truncated={payload.doc_truncated}"
            )
            lines.append(payload.doc)
            if payload.doc_truncated:
                lines.append(
                    f"Doc truncated; rerun: function {entry.function_id} "
                    f"--max-doc-chars {payload.doc_chars}"
                )
        return "\n".join(lines)

    @classmethod
    def _parameter_line(cls, parameter: FunctionParameterSpec) -> str:
        return (
            f"- {parameter.name}: required={parameter.required} "
            f"type={cls.text(parameter.annotation)} "
            f"default={cls.text(parameter.default_repr)}"
        )

    @classmethod
    def _runtime_parameter_line(cls, parameter: FunctionParameterSpec) -> str:
        return (
            f"- {parameter.name}: supplied_by={cls.text(parameter.supplied_by)} "
            f"type={cls.text(parameter.annotation)} "
            f"note={cls.quoted(parameter.description)}"
        )

    @staticmethod
    def _artifact_line(artifact: FunctionArtifactSpec) -> str:
        return f"- {artifact.name}: kind={artifact.kind} required={artifact.required}"


class AuthoringContextRenderer(McpDevOutputRenderer):
    """Compact renderer for authoring guidance."""

    output_contract = AuthoringContext
    render_options_type = AuthoringContextRenderOptions
    unavailable_summary = "Authoring context: unavailable"

    @classmethod
    def render_payload(
        cls, payload: AuthoringContext, options: AuthoringContextRenderOptions
    ) -> str:
        return "\n".join(
            (
                f"Authoring context: kind={payload.kind}",
                "Content:",
                CodeDocumentRenderOptions(max_source_chars=options.max_chars).source_text(
                    payload.content
                ),
            )
        )
