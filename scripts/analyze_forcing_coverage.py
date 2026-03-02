#!/usr/bin/env python3
"""
Forcing Coverage Analyzer

Derives everything from existing sources:
1. build_papers.py - claim extraction logic
2. papers.yaml - paper structure + forcing prefixes
3. HandleAliases.lean - forcing handles
4. Graph JSON - proof dependencies

Builds subgraph containing:
- All claim nodes
- All forcing nodes reachable from claims
- ALL intermediate nodes on paths between claims and forcing

Usage:
    python scripts/analyze_forcing_coverage.py paper4
    python scripts/analyze_forcing_coverage.py paper4 --output-graph subgraph.json
"""

import json
import re
import sys
import yaml
from pathlib import Path
from typing import Dict, Set, List, Optional, Tuple, Any
from collections import deque


def get_builder(repo_root: Path):
    """Get PaperBuilder instance from build_papers.py."""
    import importlib.util

    build_papers_path = repo_root / "scripts" / "build_papers.py"
    spec = importlib.util.spec_from_file_location("build_papers", build_papers_path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Could not load build_papers.py from {build_papers_path}")
    build_papers = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(build_papers)
    return build_papers.PaperBuilder(repo_root)


def load_papers_yaml(repo_root: Path) -> Dict:
    """Load papers.yaml."""
    with open(repo_root / "scripts" / "papers.yaml") as f:
        return yaml.safe_load(f)


def get_forcing_prefixes(papers_config: Dict, paper_id: str) -> Set[str]:
    """Get forcing prefixes for a paper from papers.yaml."""
    paper = papers_config.get("papers", {}).get(paper_id, {})
    return set(paper.get("forcing_prefixes", []))


def extract_forcing_handles(
    handle_aliases_path: Path, forcing_prefixes: Set[str]
) -> Set[str]:
    """Extract forcing handles from HandleAliases.lean."""
    text = handle_aliases_path.read_text(encoding="utf-8")
    forcing = set()

    import_match = re.search(
        r"import\s+([A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*)\.", text
    )
    module_prefix = import_match.group(1) + "." if import_match else ""

    pattern = re.compile(
        r"abbrev\s+([A-Z]+)(\d+[a-z]?)\s*:=\s*@?([A-Za-z_][A-Za-z0-9_.]*)"
    )

    for match in pattern.finditer(text):
        prefix = match.group(1)
        qualified = match.group(3)
        if prefix in forcing_prefixes:
            if module_prefix and not qualified.startswith(module_prefix):
                forcing.add(module_prefix + qualified)
            else:
                forcing.add(qualified)

    return forcing


def build_adj(nodes: List[Dict], edges: List[Dict]) -> Dict[str, List[str]]:
    """Build adjacency list. source depends on target."""
    adj = {n["id"]: [] for n in nodes}
    for e in edges:
        source = e["source"]
        target = e["target"]
        if source in adj:
            adj[source].append(target)
    return adj


def find_all_nodes_on_paths_to_forcing(
    start: str,
    adj: Dict[str, List[str]],
    forcing: Set[str],
) -> Set[str]:
    """Find ALL nodes on paths from start to forcing, PLUS what forcing depends on.

    Traces:
    1. start → ... → forcing (nodes that lead TO forcing)
    2. forcing → ... → deeper (nodes that forcing depends ON)

    Edge direction: source depends on target
    adj[source] = [targets that source depends on]
    """
    nodes_on_paths = set()

    # Phase 1: Find nodes on paths from start to forcing
    # BFS from start, collect nodes that can reach forcing
    all_reachable = {start}
    queue = deque([start])
    while queue:
        node = queue.popleft()
        for neighbor in adj.get(node, []):
            if neighbor not in all_reachable:
                all_reachable.add(neighbor)
                queue.append(neighbor)

    for node in all_reachable:
        if node == start:
            nodes_on_paths.add(node)
            continue

        # Check if this node can reach forcing
        visited = {node}
        q = deque([node])
        while q:
            n = q.popleft()
            if n in forcing:
                nodes_on_paths.add(node)
                break
            for nb in adj.get(n, []):
                if nb not in visited:
                    visited.add(nb)
                    q.append(nb)

    # Phase 2: Find what forcing theorems depend on
    # BFS FROM each reachable forcing theorem, following dependencies
    reachable_forcing = all_reachable & forcing
    for forcing_node in reachable_forcing:
        # BFS to find all dependencies of this forcing theorem
        dep_visited = {forcing_node}
        dep_queue = deque([forcing_node])
        while dep_queue:
            fn = dep_queue.popleft()
            for dep in adj.get(fn, []):  # fn depends on dep
                if dep not in dep_visited:
                    dep_visited.add(dep)
                    dep_queue.append(dep)
                    nodes_on_paths.add(dep)

    return nodes_on_paths


def build_claim_subgraph(
    graph_path: Path,
    forcing_handles: Set[str],
    claims: Dict[str, List[str]],
) -> Dict[str, Any]:
    """Build subgraph containing claims, forcing, and all intermediate nodes."""
    with open(graph_path) as f:
        data = json.load(f)

    nodes = data["nodes"]
    edges = data["edges"]
    node_ids = {n["id"] for n in nodes}

    adj = build_adj(nodes, edges)

    # Collect all nodes on paths from claims to forcing
    nodes_to_keep = set()

    for label, handles in claims.items():
        for handle in handles:
            if handle in node_ids:
                path_nodes = find_all_nodes_on_paths_to_forcing(
                    handle, adj, forcing_handles
                )
                nodes_to_keep.update(path_nodes)

    # Also keep all forcing nodes (even if not reachable)
    nodes_to_keep.update(forcing_handles & node_ids)

    # Filter nodes and edges
    filtered_nodes = [n for n in nodes if n["id"] in nodes_to_keep]
    filtered_edges = [
        e
        for e in edges
        if e["source"] in nodes_to_keep and e["target"] in nodes_to_keep
    ]

    total = len(claims)

    def reaches_forcing(start: str) -> bool:
        if start in forcing_handles:
            return True
        visited = {start}
        q = deque([start])
        while q:
            n = q.popleft()
            for nb in adj.get(n, []):
                if nb in forcing_handles:
                    return True
                if nb not in visited:
                    visited.add(nb)
                    q.append(nb)
        return False

    reaching = sum(
        1
        for label, handles in claims.items()
        if any(h in node_ids and reaches_forcing(h) for h in handles)
    )

    return {
        "total_claims": total,
        "reaching_forcing": reaching,
        "coverage_fraction": reaching / total if total > 0 else 1.0,
        "forcing_count": len(forcing_handles),
        "subgraph": {
            "nodes": filtered_nodes,
            "edges": filtered_edges,
        },
        "original_graph": {
            "nodes": len(nodes),
            "edges": len(edges),
        },
        "subgraph_stats": {
            "nodes": len(filtered_nodes),
            "edges": len(filtered_edges),
        },
    }


def analyze(paper_id: str, repo_root: Path) -> Dict[str, Any]:
    """Main entry point. Uses build_papers.py for all derivations."""
    builder = get_builder(repo_root)
    papers_config = load_papers_yaml(repo_root)

    # Get paper-specific forcing prefixes
    forcing_prefixes = get_forcing_prefixes(papers_config, paper_id)
    if not forcing_prefixes:
        print(f"Warning: No forcing_prefixes defined for {paper_id} in papers.yaml")

    claims = builder._extract_claim_label_to_lean_handles(
        paper_id, include_dependencies=True
    )

    meta = builder._get_paper_meta(paper_id)
    paper_dir = builder._get_paper_dir(paper_id)
    proofs_dir = meta.proofs_dir

    handle_aliases = None
    for p in (paper_dir / proofs_dir).rglob("HandleAliases.lean"):
        if ".lake" not in str(p):
            handle_aliases = p
            break

    if not handle_aliases:
        raise FileNotFoundError(f"HandleAliases.lean not found for {paper_id}")

    graph_path = (
        repo_root / "docs" / "papers" / "graph_infra" / "graphs" / f"{paper_id}.json"
    )
    if not graph_path.exists():
        raise FileNotFoundError(f"Graph not found: {graph_path}")

    forcing_handles = extract_forcing_handles(handle_aliases, forcing_prefixes)

    return build_claim_subgraph(graph_path, forcing_handles, claims)


def generate_report(result: Dict[str, Any], verbose: bool = False) -> str:
    """Generate formatted report."""
    lines = [
        "═══════════════════════════════════════════════════════════════",
        "                    FORCING COVERAGE REPORT                    ",
        "═══════════════════════════════════════════════════════════════",
        "",
        f"Forcing theorems: {result['forcing_count']}",
        f"Claims: {result['total_claims']}",
        "",
        f"COVERAGE: {result['reaching_forcing']}/{result['total_claims']} "
        f"({result['coverage_fraction']:.1%})",
        "",
        f"Original graph: {result['original_graph']['nodes']} nodes, {result['original_graph']['edges']} edges",
        f"Claim subgraph: {result['subgraph_stats']['nodes']} nodes, {result['subgraph_stats']['edges']} edges",
    ]

    lines.append("")
    lines.append("═══════════════════════════════════════════════════════════════")

    return "\n".join(lines)


def main():
    import argparse

    parser = argparse.ArgumentParser(description="Analyze forcing coverage")
    parser.add_argument("paper_id", help="Paper ID (e.g., paper4, paper1_jsait)")
    parser.add_argument("--verbose", "-v", action="store_true", help="Verbose output")
    parser.add_argument("--output-graph", help="Output subgraph JSON to file")

    args = parser.parse_args()

    repo_root = Path(__file__).parent.parent

    try:
        result = analyze(args.paper_id, repo_root)
    except FileNotFoundError as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)

    print(generate_report(result, args.verbose))

    if args.output_graph:
        with open(args.output_graph, "w") as f:
            json.dump(result["subgraph"], f, indent=2)
        print(f"\nSubgraph saved to {args.output_graph}")


if __name__ == "__main__":
    main()
