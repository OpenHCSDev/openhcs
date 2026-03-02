#!/usr/bin/env python3
"""
Dependency Graph Analyzer for Lean Proof Papers

Analyzes dependency graphs generated from Lean proofs to identify:
- True orphans (unreferenced lemmas/theorems)
- False positives (Lean artifacts like simp helpers)
- Handle definition inconsistencies
- Missing links between complexity infrastructure and theorems

Usage:
    python dependency_analyzer.py --graph paper4_toc.json --output analysis.json
    python dependency_analyzer.py --graph paper4_toc.json --filter --output filtered.json
"""

import json
import argparse
import sys
from collections import defaultdict
from dataclasses import dataclass, field, asdict
from typing import Dict, List, Set, Tuple, Optional
import re


# Patterns for Lean compiler artifacts that should be filtered
ARTIFACT_PATTERNS = [
    r'\._simp_',           # Simp helper lemmas
    r'\.proxyType',        # Type wrappers
    r'_aux_',              # Auxiliary definitions
    r'___macroRules_',     # Macro rules
    r'___unexpand_',       # Unexpanders
    r'\.\.',              # Internal generated names
]

# Standard library / auto-generated instance patterns (not proof clusters)
STDLIB_PATTERNS = [
    r'^elim$', r'^sizeOf_spec', r'^injEq$', r'^inj$', r'^recOn$',
    r'^noConfusion', r'^instRepr', r'^instDecidable', r'^instBEq',
    r'^instHashable', r'^instToString', r'^instOrd', r'^instInhabited',
    r'^eq_', r'^refl$', r'^irrefl$', r'^trans$', r'^antisymm$', r'^asymm$',
    r'^total$', r'^casesOn$',
]

# Handle prefix patterns used in paper
HANDLE_PREFIXES = [
    'PH', 'DC', 'CC', 'IC', 'TC', 'DE', 'MI', 'SR', 'IA', 'GE', 'IE', 'SE', 'CH', 'AC', 'DS',
    'DQ', 'DP', 'AQ', 'BB', 'BF', 'CF', 'MN', 'AN', 'PS', 'OR', 'PA', 'GN', 'FN', 'FI', 'TL',
    'CV', 'EP', 'FP', 'LP', 'IT', 'EI', 'FS', 'QT', 'WD', 'BC', 'TUR', 'W', 'XC', 'RD', 'RS', 'BA'
]


@dataclass
class ClusterInfo:
    """Information about a connected cluster in the graph."""
    id: int
    nodes: List[str]
    size: int
    is_main: bool  # Is this the largest connected component
    bridges_needed: List[Dict]  # Potential bridge theorems to connect to main


@dataclass
class AnalysisResult:
    """Results from dependency graph analysis."""
    total_nodes: int
    total_edges: int
    artifact_nodes: List[str]
    true_orphans: List[str]
    ph_handles: Dict[str, str]  # handle -> orphan status
    wip_features: List[str]
    complexity_infrastructure: List[str]
    handle_inconsistencies: List[Dict]
    clusters: List[ClusterInfo]  # Connected component analysis
    recommendations: List[str]

    def to_dict(self) -> dict:
        result = asdict(self)
        # Convert ClusterInfo objects
        if self.clusters:
            result['clusters'] = [
                {
                    'id': c.id,
                    'size': c.size,
                    'is_main': c.is_main,
                    'node_sample': c.nodes[:10],  # Limit output size
                    'bridges_needed': c.bridges_needed
                }
                for c in self.clusters
            ]
        return result


class DependencyAnalyzer:
    """Analyzes Lean dependency graphs for orphan detection and handle validation."""
    
    def __init__(self, graph_path: str):
        with open(graph_path) as f:
            self.data = json.load(f)
        
        self.nodes = self.data.get('nodes', [])
        self.edges = self.data.get('edges', [])
        self.node_ids = {n['id'] for n in self.nodes}
        
        # Build adjacency lists
        self.adj = {nid: {'out': [], 'in': []} for nid in self.node_ids}
        for edge in self.edges:
            src = edge.get('source')
            tgt = edge.get('target')
            if src in self.adj:
                self.adj[src]['out'].append(tgt)
            if tgt in self.adj:
                self.adj[tgt]['in'].append(src)
    
    def is_artifact(self, node_id: str) -> bool:
        """Check if node is a Lean compiler artifact."""
        return any(re.search(pat, node_id) for pat in ARTIFACT_PATTERNS)
    
    def get_disconnected(self) -> List[str]:
        """Get all disconnected (orphan) nodes."""
        return [nid for nid, conns in self.adj.items() 
                if not conns['out'] and not conns['in']]
    
    def categorize_orphans(self, orphans: List[str]) -> Dict[str, List[str]]:
        """Categorize orphans by type."""
        categories = {
            'ph_handles': [],
            'wip_features': [],
            'complexity_infrastructure': [],
            'simp_helpers': [],
            'other': []
        }
        
        for nid in orphans:
            base = nid.split('.')[-1]
            
            # PH handles (PH11-PH36)
            if re.match(r'PH[0-9]+$', base):
                categories['ph_handles'].append(nid)
            # WIP features
            elif any(w in nid for w in ['StateAbstraction', 'HierarchicalFactorization', 
                                        'NetworkDependency', 'stochastic_unbiased', 
                                        'continuous_unbiased', 'adaptive_query']):
                categories['wip_features'].append(nid)
            # Complexity infrastructure
            elif any(c in nid for c in ['PTIME', 'PSPACE', 'NPHard', 'BigO', 
                                        'complexity_dichotomy', 'query_computation_tradeoff']):
                categories['complexity_infrastructure'].append(nid)
            # Simp helpers
            elif '._simp_' in nid:
                categories['simp_helpers'].append(nid)
            else:
                categories['other'].append(nid)
        
        return categories
    
    def analyze_handles(self) -> Dict[str, Dict]:
        """Analyze handle definitions for consistency issues."""
        handle_analysis = {}
        
        # Find all handle nodes
        for prefix in HANDLE_PREFIXES:
            pattern = re.compile(rf'\.{prefix}[0-9]+[a-z]?$')
            matching = [nid for nid in self.node_ids if pattern.search(nid)]
            
            for nid in matching:
                base = nid.split('.')[-1]
                conns = self.adj[nid]
                
                handle_analysis[base] = {
                    'full_id': nid,
                    'is_orphan': not conns['out'] and not conns['in'],
                    'in_degree': len(conns['in']),
                    'out_degree': len(conns['out']),
                    'namespace': '.'.join(nid.split('.')[:-1]) if '.' in nid else 'root'
                }
        
        return handle_analysis
    
    def detect_handle_inconsistencies(self, handle_analysis: Dict) -> List[Dict]:
        """Detect inconsistencies in handle definitions."""
        inconsistencies = []

        # Group handles by prefix
        by_prefix = defaultdict(list)
        for name, info in handle_analysis.items():
            prefix = re.match(r'^([A-Z]+)', name)
            if prefix:
                by_prefix[prefix.group(1)].append((name, info))

        # Check for mixed orphan/connected status within same prefix
        for prefix, handles in by_prefix.items():
            orphans = [h for h in handles if h[1]['is_orphan']]
            connected = [h for h in handles if not h[1]['is_orphan']]

            if orphans and connected:
                inconsistencies.append({
                    'type': 'mixed_orphan_status',
                    'prefix': prefix,
                    'orphans': [h[0] for h in orphans],
                    'connected': [h[0] for h in connected],
                    'recommendation': f'Handles with prefix {prefix} have inconsistent '
                                    f'orphan status. Check for namespace/reference issues.'
                })

        # Check for namespace inconsistencies
        for prefix, handles in by_prefix.items():
            namespaces = set(h[1]['namespace'] for h in handles)
            if len(namespaces) > 1:
                inconsistencies.append({
                    'type': 'mixed_namespaces',
                    'prefix': prefix,
                    'namespaces': list(namespaces),
                    'handles': [h[0] for h in handles],
                    'recommendation': f'Handles with prefix {prefix} defined in multiple namespaces. '
                                    f'Standardize to single namespace.'
                })

        return inconsistencies

    def find_connected_components(self) -> List[Set[str]]:
        """Find all connected components in the graph using undirected traversal."""
        visited = set()
        components = []

        # Build undirected adjacency for component detection
        undirected = defaultdict(set)
        for nid in self.node_ids:
            undirected[nid]  # Ensure all nodes exist
        for edge in self.edges:
            src, tgt = edge.get('source'), edge.get('target')
            if src and tgt:
                undirected[src].add(tgt)
                undirected[tgt].add(src)

        def dfs(node: str, component: Set[str]):
            stack = [node]
            while stack:
                current = stack.pop()
                if current not in visited:
                    visited.add(current)
                    component.add(current)
                    for neighbor in undirected[current]:
                        if neighbor not in visited:
                            stack.append(neighbor)

        for nid in self.node_ids:
            if nid not in visited:
                component = set()
                dfs(nid, component)
                components.append(component)

        return components

    def is_stdlib_artifact(self, node_id: str) -> bool:
        """Check if node is a Lean standard library auto-generated definition."""
        base_name = node_id.split('.')[-1]
        return any(re.match(pat, base_name) for pat in STDLIB_PATTERNS)

    def find_bridge_candidates(self, cluster_nodes: Set[str], main_nodes: Set[str]) -> List[Dict]:
        """Find potential bridge theorems between a cluster and the main component.

        A bridge candidate is a node in the cluster that:
        1. Has high out-degree (likely to be a theorem that should reference main)
        2. Or has a name suggesting it's a major theorem (not a helper)
        3. Is NOT a standard library auto-generated definition
        """
        candidates = []

        for node in cluster_nodes:
            # Skip standard library artifacts
            if self.is_stdlib_artifact(node):
                continue

            conns = self.adj[node]
            out_degree = len(conns['out'])
            in_degree = len(conns['in'])
            base_name = node.split('.')[-1]

            # Score based on characteristics of a bridge theorem
            score = 0
            reasons = []

            # High out-degree suggests it's a main theorem
            if out_degree >= 3:
                score += 2
                reasons.append(f"high out-degree ({out_degree})")

            # Theorem-like names (not helpers)
            if any(kw in base_name for kw in ['theorem', 'Theorem', 'main', 'Main']):
                score += 3
                reasons.append("theorem-like name")

            # Handle references suggest it's a claim
            if re.match(r'^[A-Z]{2,}[0-9]+', base_name):
                score += 2
                reasons.append("handle reference")

            # Low in-degree suggests it might be a root that should connect
            if in_degree == 0 and out_degree > 0:
                score += 1
                reasons.append("root node with dependents")

            if score >= 2:
                candidates.append({
                    'node': node,
                    'score': score,
                    'reasons': reasons,
                    'out_degree': out_degree,
                    'in_degree': in_degree,
                    'suggested_bridge': f"Add dependency from {node} to a main theorem"
                })

        # Sort by score descending
        candidates.sort(key=lambda x: x['score'], reverse=True)
        return candidates[:5]  # Return top 5

    def analyze_clusters(self) -> List[ClusterInfo]:
        """Analyze connected components to find isolated clusters needing bridges."""
        components = self.find_connected_components()

        if not components:
            return []

        # Sort by size descending - largest is the main component
        components.sort(key=len, reverse=True)
        main_component = components[0]

        clusters = []
        for i, comp in enumerate(components):
            is_main = (i == 0)
            nodes_list = list(comp)

            # Find bridge candidates if this is not the main component
            bridges_needed = []
            if not is_main:
                bridges_needed = self.find_bridge_candidates(comp, main_component)

            clusters.append(ClusterInfo(
                id=i,
                nodes=nodes_list,
                size=len(comp),
                is_main=is_main,
                bridges_needed=bridges_needed
            ))

        return clusters
    
    def generate_recommendations(self, categories: Dict, inconsistencies: List,
                                   clusters: List[ClusterInfo]) -> List[str]:
        """Generate actionable recommendations."""
        recs = []

        # Artifact recommendations
        if categories['simp_helpers']:
            recs.append(f"Filter {len(categories['simp_helpers'])} simp helper artifacts from visualization")

        # PH handle recommendations
        if categories['ph_handles']:
            recs.append(f"PH handles ({len(categories['ph_handles'])} found) appear orphaned due to "
                       f"@PhysicalComplexity namespace references - verify in HandleAliases.lean")

        # Inconsistency recommendations
        for inc in inconsistencies:
            recs.append(inc['recommendation'])

        # Complexity infrastructure
        if categories['complexity_infrastructure']:
            recs.append(f"Complexity infrastructure ({len(categories['complexity_infrastructure'])} items) "
                       f"may need explicit links from theorems that use them")

        # Cluster/bridge recommendations
        isolated_clusters = [c for c in clusters if not c.is_main and c.size > 1]
        if isolated_clusters:
            recs.append(f"Found {len(isolated_clusters)} isolated cluster(s) disconnected from main graph")
            for cluster in isolated_clusters:
                if cluster.bridges_needed:
                    top_bridge = cluster.bridges_needed[0]
                    recs.append(f"  Cluster {cluster.id} (size {cluster.size}): "
                               f"Consider adding bridge from {top_bridge['node'].split('.')[-1]}")

        return recs
    
    def analyze(self) -> AnalysisResult:
        """Run full analysis."""
        # Find artifacts
        artifacts = [nid for nid in self.node_ids if self.is_artifact(nid)]

        # Find true orphans (excluding artifacts)
        real_nodes = self.node_ids - set(artifacts)
        orphans = [nid for nid in real_nodes
                   if not self.adj[nid]['out'] and not self.adj[nid]['in']]

        # Categorize
        categories = self.categorize_orphans(orphans)

        # Analyze handles
        handle_analysis = self.analyze_handles()

        # Detect inconsistencies
        inconsistencies = self.detect_handle_inconsistencies(handle_analysis)

        # Analyze clusters
        clusters = self.analyze_clusters()

        # Generate recommendations
        recommendations = self.generate_recommendations(categories, inconsistencies, clusters)

        return AnalysisResult(
            total_nodes=len(self.nodes),
            total_edges=len(self.edges),
            artifact_nodes=artifacts,
            true_orphans=orphans,
            ph_handles={h: 'orphan' for h in categories['ph_handles']},
            wip_features=categories['wip_features'],
            complexity_infrastructure=categories['complexity_infrastructure'],
            handle_inconsistencies=inconsistencies,
            clusters=clusters,
            recommendations=recommendations
        )
    
    def filter_artifacts(self, output_path: str):
        """Create filtered graph without artifacts."""
        filtered_nodes = [n for n in self.nodes if not self.is_artifact(n['id'])]
        artifact_ids = {n['id'] for n in self.nodes if self.is_artifact(n['id'])}
        filtered_edges = [e for e in self.edges 
                         if e['source'] not in artifact_ids and e['target'] not in artifact_ids]
        
        filtered_data = {
            'nodes': filtered_nodes,
            'edges': filtered_edges
        }
        
        with open(output_path, 'w') as f:
            json.dump(filtered_data, f, indent=2)
        
        print(f"Filtered graph saved to {output_path}")
        print(f"  Original: {len(self.nodes)} nodes, {len(self.edges)} edges")
        print(f"  Filtered: {len(filtered_nodes)} nodes, {len(filtered_edges)} edges")
        print(f"  Removed: {len(artifact_ids)} artifacts")


def main():
    parser = argparse.ArgumentParser(description='Analyze Lean dependency graphs')
    parser.add_argument('--graph', required=True, help='Path to dependency graph JSON')
    parser.add_argument('--output', help='Path for analysis output JSON')
    parser.add_argument('--filter', action='store_true', help='Filter artifacts and save cleaned graph')
    parser.add_argument('--filter-output', default='filtered_graph.json', 
                       help='Output path for filtered graph')
    parser.add_argument('--verbose', '-v', action='store_true', help='Verbose output')
    
    args = parser.parse_args()
    
    try:
        analyzer = DependencyAnalyzer(args.graph)
    except Exception as e:
        print(f"Error loading graph: {e}", file=sys.stderr)
        sys.exit(1)
    
    if args.filter:
        analyzer.filter_artifacts(args.filter_output)
    
    # Always run analysis
    result = analyzer.analyze()
    
    if args.verbose:
        print(f"\n=== Dependency Graph Analysis ===")
        print(f"Total nodes: {result.total_nodes}")
        print(f"Total edges: {result.total_edges}")
        print(f"Artifact nodes: {len(result.artifact_nodes)}")
        print(f"True orphans: {len(result.true_orphans)}")
        print(f"PH handles: {len(result.ph_handles)}")

        if result.clusters:
            print(f"\n=== Cluster Analysis ===")
            print(f"Total clusters: {len(result.clusters)}")
            main_cluster = next((c for c in result.clusters if c.is_main), None)
            if main_cluster:
                print(f"Main cluster size: {main_cluster.size} nodes")
            isolated = [c for c in result.clusters if not c.is_main and c.size > 1]
            if isolated:
                print(f"\nIsolated clusters needing bridges:")
                for cluster in isolated:
                    print(f"  Cluster {cluster.id}: {cluster.size} nodes")
                    if cluster.bridges_needed:
                        top = cluster.bridges_needed[0]
                        print(f"    Top bridge candidate: {top['node'].split('.')[-1]}")
                        print(f"      Score: {top['score']}, Reasons: {', '.join(top['reasons'])}")

        print(f"\n=== Recommendations ===")
        for i, rec in enumerate(result.recommendations, 1):
            print(f"{i}. {rec}")

        if result.handle_inconsistencies:
            print(f"\n=== Handle Inconsistencies ===")
            for inc in result.handle_inconsistencies:
                print(f"\n{inc['type']}: {inc['prefix']}")
                if 'orphans' in inc:
                    print(f"  Orphans: {', '.join(inc['orphans'][:5])}")
                    if len(inc['orphans']) > 5:
                        print(f"  ... and {len(inc['orphans'])-5} more")
    
    if args.output:
        with open(args.output, 'w') as f:
            json.dump(result.to_dict(), f, indent=2)
        print(f"\nAnalysis saved to {args.output}")


if __name__ == '__main__':
    main()
