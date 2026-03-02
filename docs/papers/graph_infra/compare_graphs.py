#!/usr/bin/env python3
"""
Compare two exported proof dependency graphs (JSON) for node/edge overlap.

Usage: python compare_graphs.py graphA.json graphB.json
Reports counts, intersection sizes, and whether A contains B (nodes/edges).
"""
import json
import sys
from pathlib import Path


def load_graph(p):
    with open(p) as f:
        data = json.load(f)
    nodes = {n['id'] for n in data.get('nodes', [])}
    edges = {(e['source'] if isinstance(e['source'], str) else e['source']['id'],
              e['target'] if isinstance(e['target'], str) else e['target']['id']) for e in data.get('edges', [])}
    return nodes, edges


def main():
    if len(sys.argv) < 3:
        print('Usage: compare_graphs.py A.json B.json')
        sys.exit(2)
    a_path = Path(sys.argv[1])
    b_path = Path(sys.argv[2])
    if not a_path.exists():
        print(f'File not found: {a_path}')
        sys.exit(1)
    if not b_path.exists():
        print(f'File not found: {b_path}')
        sys.exit(1)

    a_nodes, a_edges = load_graph(a_path)
    b_nodes, b_edges = load_graph(b_path)

    print(f'A: {len(a_nodes)} nodes, {len(a_edges)} edges')
    print(f'B: {len(b_nodes)} nodes, {len(b_edges)} edges')

    nodes_inter = a_nodes & b_nodes
    edges_inter = a_edges & b_edges
    print(f'Intersection: {len(nodes_inter)} shared nodes, {len(edges_inter)} shared edges')

    only_in_a = a_nodes - b_nodes
    only_in_b = b_nodes - a_nodes
    print(f'Only in A: {len(only_in_a)} nodes; Only in B: {len(only_in_b)} nodes')

    print('\nContainment checks:')
    print(f'A contains all B nodes? {b_nodes.issubset(a_nodes)}')
    print(f'A contains all B edges? {b_edges.issubset(a_edges)}')
    print(f'B contains all A nodes? {a_nodes.issubset(b_nodes)}')
    print(f'B contains all A edges? {a_edges.issubset(b_edges)}')

    if len(nodes_inter) > 0:
        sample = list(nodes_inter)[:10]
        print('\nSample shared node ids:')
        for s in sample:
            print('  ', s)


if __name__ == '__main__':
    main()
