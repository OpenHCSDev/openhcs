#!/usr/bin/env python3
"""
Automated fix for PH handles in dependency graph.

Handles that use @PhysicalComplexity.* notation cannot be changed in Lean
(require @ notation for universe polymorphism), so this script automatically
adds the missing edges to the dependency graph JSON.

Also handles PH.* references that may be missing edges due to namespace exports.
"""

import json
import re
from pathlib import Path


def parse_handle_aliases(lean_file: Path) -> tuple[dict[str, str], dict[str, str]]:
    """
    Parse HandleAliases.lean to find:
    1. Handles using @PhysicalComplexity.* notation (need explicit edges)
    2. Handles using PH.* notation (should have edges through PH namespace)
    
    Returns tuple of (physical_complexity_handles, ph_namespace_handles)
    """
    content = lean_file.read_text()
    
    # Find handles using @PhysicalComplexity.* (need manual edge fix)
    pc_pattern = r'abbrev\s+(PH\d+)\s*:=\s*@PhysicalComplexity\.(\w+)'
    pc_matches = re.findall(pc_pattern, content)
    pc_handles = {handle: theorem for handle, theorem in pc_matches}
    
    # Find handles using PH.* (should connect through PH namespace)
    ph_pattern = r'abbrev\s+(PH\d+)\s*:=\s*PH\.(\w+)'
    ph_matches = re.findall(ph_pattern, content)
    ph_handles = {handle: theorem for handle, theorem in ph_matches}
    
    return pc_handles, ph_handles


def find_target_module(graph_data: dict, module_name: str) -> str | None:
    """Find a module node ID containing the given name."""
    for node in graph_data.get('nodes', []):
        node_id = node.get('id', '')
        if module_name in node_id:
            return node_id
    return None


def find_handle_nodes(graph_data: dict, handles: dict[str, str]) -> dict[str, str]:
    """Find node IDs for the given handles in the graph."""
    handle_nodes = {}
    for node in graph_data.get('nodes', []):
        node_id = node.get('id', '')
        # Check if this node is one of our handles
        for handle in handles.keys():
            # Match either .PH## suffix or exact match
            if node_id.endswith(f'.{handle}') or node_id == handle:
                handle_nodes[handle] = node_id
                break
    return handle_nodes


def add_missing_edges(graph_data: dict, handles: dict[str, str], target_module: str, 
                       relationship: str = 'references') -> dict:
    """Add edges from handles to target module."""
    # Find handle nodes
    handle_nodes = find_handle_nodes(graph_data, handles)
    
    # Get existing edges to avoid duplicates
    existing_edges = set()
    for edge in graph_data.get('edges', []):
        source = edge.get('source', '')
        target = edge.get('target', '')
        existing_edges.add((source, target))
    
    # Add new edges
    new_edges = []
    for handle, theorem in handles.items():
        if handle in handle_nodes:
            source = handle_nodes[handle]
            target = target_module
            
            if (source, target) not in existing_edges:
                new_edge = {
                    'source': source,
                    'target': target,
                    'relationship': relationship,
                    'sourceHandle': handle,
                    'targetTheorem': theorem,
                    'autoFixed': True
                }
                new_edges.append(new_edge)
                existing_edges.add((source, target))
                print(f"  Added edge: {handle} -> {target_module}")
    
    if new_edges:
        graph_data['edges'].extend(new_edges)
    
    return graph_data, len(new_edges)


def main():
    # Paths
    lean_file = Path('docs/papers/paper4_decision_quotient/proofs/DecisionQuotient/HandleAliases.lean')
    graph_file = Path('docs/papers/paper4_decision_quotient/releases/arxiv_package_paper4_toc/graphs/paper4_toc.json')
    output_file = graph_file
    
    print("=" * 60)
    print("PH Handle Dependency Graph Fixer")
    print("=" * 60)
    
    # Parse Lean file
    print(f"\nParsing {lean_file}...")
    pc_handles, ph_handles = parse_handle_aliases(lean_file)
    
    print(f"\nFound {len(pc_handles)} handles using @PhysicalComplexity.* notation:")
    for handle, theorem in pc_handles.items():
        print(f"  {handle} -> PhysicalComplexity.{theorem}")
    
    print(f"\nFound {len(ph_handles)} handles using PH.* notation:")
    for handle, theorem in ph_handles.items():
        print(f"  {handle} -> PH.{theorem}")
    
    # Load graph
    print(f"\nLoading dependency graph from {graph_file}...")
    with open(graph_file, 'r') as f:
        graph_data = json.load(f)
    
    print(f"Graph has {len(graph_data.get('nodes', []))} nodes and {len(graph_data.get('edges', []))} edges")
    
    total_added = 0
    
    # Add edges for @PhysicalComplexity.* handles
    if pc_handles:
        print("\nAdding edges for @PhysicalComplexity.* handles...")
        # Find PhysicalComplexity module
        pc_module = find_target_module(graph_data, 'PhysicalComplexity')
        if not pc_module:
            pc_module = "PhysicalComplexity.PhysicalHardness"
            print(f"  (Using fallback target: {pc_module})")
        
        graph_data, added = add_missing_edges(graph_data, pc_handles, pc_module, 'referencesPhysicalComplexity')
        total_added += added
    
    # Add edges for PH.* handles (they should reference through PH namespace)
    if ph_handles:
        print("\nAdding edges for PH.* handles...")
        # Find PH namespace module (DecisionQuotient.PH)
        ph_module = find_target_module(graph_data, 'DecisionQuotient.PH')
        if not ph_module:
            # Try to find DecisionQuotient.HandleAliases which exports PH
            ph_module = find_target_module(graph_data, 'DecisionQuotient.HandleAliases')
        if not ph_module:
            ph_module = "DecisionQuotient.PH"
            print(f"  (Using fallback target: {ph_module})")
        
        graph_data, added = add_missing_edges(graph_data, ph_handles, ph_module, 'referencesPHNamespace')
        total_added += added
    
    # Save updated graph
    print(f"\nSaving updated graph to {output_file}...")
    with open(output_file, 'w') as f:
        json.dump(graph_data, f, indent=2)
    
    print("\n" + "=" * 60)
    print(f"Done! Added {total_added} missing edges to dependency graph.")
    print("All PH handles should now be properly connected.")
    print("=" * 60)


if __name__ == '__main__':
    main()
