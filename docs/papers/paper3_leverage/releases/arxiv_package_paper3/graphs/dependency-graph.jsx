import { useState, useEffect, useRef, useCallback, useMemo } from "react";
import * as d3 from "d3";
import { computeStats, isArtifact, buildAdj, findRoots, bfs, FILTERS, applyFilters, shortestPath, validateTruePaths, distancesFromRoots, findAllPaths, generateValidationReport } from "./graph_utils";
import { FOUNDATION_BUCKETS, extractLatex, renderLatex, formatLeanSignature } from "./latex_renderer";

const EMPTY_DATA = { nodes: [], edges: [] };

function clusterKeyForNode(node) {
  if (!node) return "unknown";
  if (isFoundationNode(node)) return "FOUNDATION";
  const parts = String(node.id || "").split(".");
  if (parts.length >= 2) return `${parts[0]}.${parts[1]}`;
  return parts[0] || "unknown";
}

function clusterLabelForKey(key) {
  if (key === "FOUNDATION") return "Foundation";
  return key;
}

function buildNamespaceClusters(data) {
  if (!data?.nodes?.length) return EMPTY_DATA;

  const groups = new Map();
  for (const node of data.nodes) {
    const key = clusterKeyForNode(node);
    if (!groups.has(key)) groups.set(key, []);
    groups.get(key).push(node);
  }

  const nodes = [];
  const edgeKeys = new Set();
  const edges = [];

  for (const [key, members] of groups.entries()) {
    const semanticKinds = members.map((node) => nodeSemanticKind(node));
    const kind = semanticKinds.includes("foundationAxiom") || semanticKinds.includes("localAxiom")
      ? "axiom"
      : semanticKinds.includes("theorem")
        ? "theorem"
        : semanticKinds.includes("definition")
          ? "definition"
          : "other";
    nodes.push({
      id: `CLUSTER:${key}`,
      kind,
      cluster: true,
      clusterKey: key,
      clusterLabel: clusterLabelForKey(key),
      memberCount: members.length,
    });
  }

  const nodeToCluster = new Map();
  for (const node of data.nodes) {
    nodeToCluster.set(node.id, `CLUSTER:${clusterKeyForNode(node)}`);
  }

  for (const edge of data.edges || []) {
    const source = typeof edge.source === "object" ? edge.source.id : edge.source;
    const target = typeof edge.target === "object" ? edge.target.id : edge.target;
    const clusterSource = nodeToCluster.get(source);
    const clusterTarget = nodeToCluster.get(target);
    if (!clusterSource || !clusterTarget || clusterSource === clusterTarget) continue;
    const key = `${clusterSource}->${clusterTarget}`;
    if (edgeKeys.has(key)) continue;
    edgeKeys.add(key);
    edges.push({ source: clusterSource, target: clusterTarget });
  }

  return { nodes, edges };
}

function LatexBlock({ latex, fallback }) {
  const ref = useRef(null);

  useEffect(() => {
    if (!ref.current) return;
    if (!latex) {
      ref.current.textContent = fallback || "";
      return;
    }
    if (typeof window !== "undefined" && window.katex) {
      renderLatex(latex, ref.current);
      return;
    }
    ref.current.textContent = fallback || latex;
  }, [latex, fallback]);

  return <div ref={ref} />;
}

function normalizeManifest(manifest) {
  const rawGraphs = Array.isArray(manifest)
    ? manifest
    : Array.isArray(manifest?.graphs)
      ? manifest.graphs
      : [];
  const graphs = rawGraphs
    .map((entry) => {
      if (typeof entry === "string") {
        return { file: entry, label: entry.replace(/\.json$/, "") };
      }
      if (!entry || typeof entry.file !== "string") {
        return null;
      }
      return {
        file: entry.file,
        label: entry.label || entry.file.replace(/\.json$/, ""),
      };
    })
    .filter(Boolean);
  const manifestDefault = typeof manifest?.default === "string" ? manifest.default : "";
  const defaultFile = graphs.some((entry) => entry.file === manifestDefault)
    ? manifestDefault
    : (graphs[0]?.file || "");
  return { graphs, defaultFile };
}

const NODE_KIND_COLORS = {
  theorem: "#3b82f6",
  definition: "#8b5cf6",
  localAxiom: "#94a3b8",
  foundationAxiom: "#f59e0b",
  other: "#6b7280",
};

const SCOPE_PALETTE = [
  "#22c55e",
  "#06b6d4",
  "#ec4899",
  "#f97316",
  "#a855f7",
  "#eab308",
  "#14b8a6",
  "#84cc16",
  "#f43f5e",
  "#38bdf8",
];

function isFoundationNode(node) {
  return String(node?.id || "").startsWith("FOUNDATION.");
}

function nodeSemanticKind(node) {
  if (!node) return "other";
  if (node.kind === "definition") return "definition";
  if (node.kind === "axiom") return isFoundationNode(node) ? "foundationAxiom" : "localAxiom";
  if (node.kind === "theorem") return "theorem";
  return "other";
}

function nodeFillColor(node) {
  return NODE_KIND_COLORS[nodeSemanticKind(node)] || NODE_KIND_COLORS.other;
}

function nodeRadius(node) {
  if (node?.cluster) {
    return Math.max(10, Math.min(24, 8 + Math.log2((node.memberCount || 1) + 1) * 3));
  }
  switch (nodeSemanticKind(node)) {
    case "foundationAxiom":
      return 5.5;
    case "localAxiom":
      return 5;
    case "definition":
      return 4;
    case "theorem":
      return 3.5;
    default:
      return 3;
  }
}

function scopeKeyForNode(node) {
  if (!node) return "unknown";
  if (isFoundationNode(node)) return "FOUNDATION";
  const id = String(node.id || "");
  const [root] = id.split(".");
  return root || "unknown";
}

function scopeLabelForKey(key) {
  if (key === "FOUNDATION") return "Foundation";
  return key;
}

function sortScopeKeys(a, b) {
  if (a === "FOUNDATION") return -1;
  if (b === "FOUNDATION") return 1;
  return a.localeCompare(b);
}

const KIND_SHAPES = {
  theorem: "circle",
  definition: "square",
  axiom: "diamond",
  other: "circle",
};

// computeStats provided by graph_utils.js (imported above)

function ForceGraph({ data, width, height, highlightScope, scopeColors, selectedNode, onSelectNode, highlightedPath }) {
  const svgRef = useRef(null);
  const simRef = useRef(null);
  const nodePositionsRef = useRef({});
  const baseStroke = useCallback(
    (d) => scopeColors[scopeKeyForNode(d)] || "#52525b",
    [scopeColors]
  );

  useEffect(() => {
    if (!svgRef.current) return;

    const svg = d3.select(svgRef.current);
    svg.selectAll("*").remove();

    const g = svg.append("g");

    // Zoom
    const zoom = d3.zoom().scaleExtent([0.1, 8]).on("zoom", (event) => {
      g.attr("transform", event.transform);
    });
    svg.call(zoom);

    const nodes = data.nodes.map((d) => ({ ...d }));
    const edges = data.edges.map((d) => ({ ...d }));

    const anyClusters = nodes.some((d) => d.cluster);

    const sim = d3
      .forceSimulation(nodes)
      .force(
        "link",
        d3
          .forceLink(edges)
          .id((d) => d.id)
          .distance(anyClusters ? 70 : 15)
          .strength(anyClusters ? 0.18 : 0.3)
      )
      .force("charge", d3.forceManyBody().strength(anyClusters ? -70 : -8).distanceMax(anyClusters ? 260 : 150))
      .force("center", d3.forceCenter(width / 2, height / 2))
      .force("collision", d3.forceCollide().radius((d) => (d.cluster ? Math.max(18, 8 + Math.log2((d.memberCount || 1) + 1) * 4) : 4)))
      .force(
        "cluster",
        d3.forceX(width / 2).strength(anyClusters ? 0.03 : 0.01)
      )
      .force("clusterY", d3.forceY(height / 2).strength(anyClusters ? 0.03 : 0.01));

    simRef.current = sim;

    const link = g
      .append("g")
      .selectAll("line")
      .data(edges)
      .join("line")
      .attr("stroke", "#ffffff08")
      .attr("stroke-width", 0.5);

    const node = g
      .append("g")
      .selectAll("circle")
      .data(nodes)
      .join("circle")
      .attr("r", (d) => nodeRadius(d))
      .attr("fill", (d) => nodeFillColor(d))
      .attr("stroke", (d) => baseStroke(d))
      .attr("stroke-width", 1.4)
      .attr("opacity", 0.85)
      .call(
        d3
          .drag()
          .on("start", (event, d) => {
            if (!event.active) sim.alphaTarget(0.3).restart();
            d.fx = d.x;
            d.fy = d.y;
          })
          .on("drag", (event, d) => {
            d.fx = event.x;
            d.fy = event.y;
          })
          .on("end", (event, d) => {
            if (!event.active) sim.alphaTarget(0);
            d.fx = null;
            d.fy = null;
          })
      );

    node.append("title").text((d) => `${d.cluster ? `${d.clusterLabel} (${d.memberCount})` : d.id} (${d.kind})`);

    const labels = g
      .append("g")
      .selectAll("text")
      .data(nodes.filter((d) => d.cluster))
      .join("text")
      .attr("fill", "#cbd5e1")
      .attr("font-size", 10)
      .attr("text-anchor", "middle")
      .attr("pointer-events", "none")
      .text((d) => `${d.clusterLabel} (${d.memberCount})`);

    node.on("click", (event, d) => {
      event.stopPropagation();
      if (onSelectNode) onSelectNode(d);
    });

    sim.on("tick", () => {
      link
        .attr("x1", (d) => d.source.x)
        .attr("y1", (d) => d.source.y)
        .attr("x2", (d) => d.target.x)
        .attr("y2", (d) => d.target.y);
      node
        .attr("cx", (d) => d.x)
        .attr("cy", (d) => d.y)
        .each((d) => {
          nodePositionsRef.current[d.id] = { x: d.x, y: d.y };
        });
      labels
        .attr("x", (d) => d.x)
        .attr("y", (d) => (d.y || 0) - Math.max(12, nodeRadius(d) + 6));
    });

    // Highlight paper on hover
    if (highlightScope !== null) {
      node
        .attr("opacity", (d) =>
          scopeKeyForNode(d) === highlightScope ? 1 : 0.08
        )
        .attr("r", (d) =>
          scopeKeyForNode(d) === highlightScope ? nodeRadius(d) + 1.5 : nodeRadius(d)
        );
      link.attr("stroke", (d) => {
        const s = typeof d.source === "object" ? d.source : nodes.find((n) => n.id === d.source);
        const t = typeof d.target === "object" ? d.target : nodes.find((n) => n.id === d.target);
        return scopeKeyForNode(s) === highlightScope || scopeKeyForNode(t) === highlightScope
          ? (scopeColors[highlightScope] || "#94a3b8") + "66"
          : "#ffffff03";
      });
    } else {
      node
        .attr("opacity", 0.85)
        .attr("r", (d) => nodeRadius(d));
      link.attr("stroke", "#ffffff08");
    }

    return () => sim.stop();
  }, [data, width, height, highlightScope, baseStroke, scopeColors]);

  useEffect(() => {
    if (!svgRef.current) return;
    const svg = d3.select(svgRef.current);
    const node = svg.selectAll("circle");
    const link = svg.selectAll("line");
    
    if (!highlightedPath || highlightedPath.length < 2) {
      return;
    }
    
    const pathSet = new Set(highlightedPath);
    const edgeSet = new Set();
    for (let i = 0; i < highlightedPath.length - 1; i++) {
      edgeSet.add(`${highlightedPath[i]}->${highlightedPath[i + 1]}`);
    }
    
    node.attr("opacity", (d) => pathSet.has(d.id) ? 1 : 0.15)
        .attr("r", (d) => {
          if (!pathSet.has(d.id)) return nodeRadius(d);
          return nodeRadius(d) + 2;
        })
        .attr("stroke", (d) => pathSet.has(d.id) ? "#fff" : (d.id === selectedNode ? "#fff" : baseStroke(d)))
        .attr("stroke-width", (d) => pathSet.has(d.id) ? 2.4 : (d.id === selectedNode ? 2.2 : 1.4));
    
    link.attr("stroke", (d) => {
      const s = typeof d.source === "object" ? d.source.id : d.source;
      const t = typeof d.target === "object" ? d.target.id : d.target;
      return edgeSet.has(`${s}->${t}`) ? "#3b82f6" : "#ffffff05";
    })
    .attr("stroke-width", (d) => {
      const s = typeof d.source === "object" ? d.source.id : d.source;
      const t = typeof d.target === "object" ? d.target.id : d.target;
      return edgeSet.has(`${s}->${t}`) ? 2 : 0.5;
    });
  }, [highlightedPath, baseStroke, selectedNode]);

  useEffect(() => {
    if (!svgRef.current || !selectedNode) return;
    const pos = nodePositionsRef.current[selectedNode];
    if (!pos) return;
    const svg = d3.select(svgRef.current);
    const zoom = d3.zoomTransform(svg.node());
    const scale = 2;
    const tx = width / 2 - pos.x * scale;
    const ty = height / 2 - pos.y * scale;
    svg.transition().duration(500).call(
      d3.zoom().transform,
      d3.zoomIdentity.translate(tx, ty).scale(scale)
    );
  }, [selectedNode, width, height]);

  useEffect(() => {
    if (!svgRef.current) return;
    const svg = d3.select(svgRef.current);
    const node = svg.selectAll("circle");
    node.attr("stroke", (d) => d.id === selectedNode ? "#fff" : baseStroke(d))
        .attr("stroke-width", (d) => d.id === selectedNode ? 2.2 : 1.4);
  }, [selectedNode, baseStroke]);

  return (
    <svg
      ref={svgRef}
      width={width}
      height={height}
      style={{ background: "#0a0a0a", borderRadius: 8 }}
    />
  );
}

export default function DependencyGraphViewer() {
  const [data, setData] = useState(EMPTY_DATA);
  const [availableGraphs, setAvailableGraphs] = useState([]);
  const [selectedGraphFile, setSelectedGraphFile] = useState("");
  const [graphLoadError, setGraphLoadError] = useState("");
  const [declInfo, setDeclInfo] = useState({});
  const [highlightScope, setHighlightScope] = useState(null);
  const [jsonInput, setJsonInput] = useState("");
  const [customData, setCustomData] = useState(null);
  const rawData = customData || data;
  const [hideArtifacts, setHideArtifacts] = useState(true);
  const [viewMode, setViewMode] = useState('forcing'); // 'forcing' | 'claims' | 'full' | 'audit'
  const [collapseNamespaces, setCollapseNamespaces] = useState(true);
  const [traceNode, setTraceNode] = useState("");
  const [tracePath, setTracePath] = useState(null);
  const [additionalJson, setAdditionalJson] = useState("");
  const [restrictScope, setRestrictScope] = useState(null);
  const [depthLimit, setDepthLimit] = useState(null);
  const [activeFilters, setActiveFilters] = useState([]);
  const [selectedNode, setSelectedNode] = useState(null);
  const [showAuditPanel, setShowAuditPanel] = useState(false);
  // Node Search state
  const [nodeSearchQuery, setNodeSearchQuery] = useState("");
  const [searchKindFilter, setSearchKindFilter] = useState(null);
  const [searchScopeFilter, setSearchScopeFilter] = useState(null);
  const [searchSort, setSearchSort] = useState('name');
  const [focusedSearchIndex, setFocusedSearchIndex] = useState(0);
  const loadNonceRef = useRef(String(Date.now()));
  const searchInputRef = useRef(null);
  const filteredData = useMemo(
    () => applyFilters(rawData, activeFilters),
    [rawData, activeFilters]
  );
  const activeData = useMemo(() => {
    if (!restrictScope) return filteredData;
    const allowed = new Set(
      filteredData.nodes
        .filter((node) => scopeKeyForNode(node) === restrictScope)
        .map((node) => node.id)
    );
    return {
      nodes: filteredData.nodes.filter((node) => allowed.has(node.id)),
      edges: filteredData.edges.filter((edge) => {
        const source = typeof edge.source === "object" ? edge.source.id : edge.source;
        const target = typeof edge.target === "object" ? edge.target.id : edge.target;
        return allowed.has(source) && allowed.has(target);
      }),
    };
  }, [filteredData, restrictScope]);
  const stats = useMemo(
    () => computeStats(activeData),
    [activeData]
  );
  const activeNodeKindCounts = useMemo(() => {
    let theorem = 0;
    let definition = 0;
    let localAxiom = 0;
    let foundationAxiom = 0;
    for (const node of activeData.nodes || []) {
      const semantic = nodeSemanticKind(node);
      if (semantic === "theorem") theorem += 1;
      else if (semantic === "definition") definition += 1;
      else if (semantic === "localAxiom") localAxiom += 1;
      else if (semantic === "foundationAxiom") foundationAxiom += 1;
    }
    return { theorem, definition, localAxiom, foundationAxiom };
  }, [activeData]);
  const scopeMeta = useMemo(() => {
    const keys = Array.from(new Set((rawData.nodes || []).map((node) => scopeKeyForNode(node)))).sort(sortScopeKeys);
    const colors = {};
    let paletteIndex = 0;
    for (const key of keys) {
      if (key === "FOUNDATION") {
        colors[key] = NODE_KIND_COLORS.foundationAxiom;
      } else {
        colors[key] = SCOPE_PALETTE[paletteIndex % SCOPE_PALETTE.length];
        paletteIndex += 1;
      }
    }
    return {
      entries: keys.map((key) => ({
        key,
        label: scopeLabelForKey(key),
        color: colors[key],
      })),
      colors,
    };
  }, [rawData]);
  const scopeLabelMap = useMemo(
    () => Object.fromEntries(scopeMeta.entries.map((entry) => [entry.key, entry.label])),
    [scopeMeta]
  );

  useEffect(() => {
    let cancelled = false;
    const loadManifest = async () => {
      try {
        const response = await fetch(`manifest.json?v=${loadNonceRef.current}`);
        if (!response.ok) {
          throw new Error(`manifest.json unavailable (${response.status})`);
        }
        const parsed = normalizeManifest(await response.json());
        if (cancelled) return;
        setAvailableGraphs(parsed.graphs);
        const requested = new URLSearchParams(window.location.search).get("graph");
        const chosen = parsed.graphs.find(
          (entry) => entry.file === requested || entry.label === requested
        )?.file || parsed.defaultFile;
        setSelectedGraphFile(chosen);
        setGraphLoadError(chosen ? "" : "No graph files listed in manifest.json");
      } catch (err) {
        if (cancelled) return;
        setAvailableGraphs([]);
        setSelectedGraphFile("");
        setGraphLoadError(err.message);
      }
    };
    loadManifest();
    return () => {
      cancelled = true;
    };
  }, []);

  useEffect(() => {
    if (!selectedGraphFile) return;
    const url = new URL(window.location.href);
    if (url.searchParams.get("graph") !== selectedGraphFile) {
      url.searchParams.set("graph", selectedGraphFile);
      window.history.replaceState({}, "", url);
    }
  }, [selectedGraphFile]);

  useEffect(() => {
    if (!selectedGraphFile) return;
    let cancelled = false;
    const loadGraph = async () => {
      try {
        const response = await fetch(`${selectedGraphFile}?v=${loadNonceRef.current}`);
        if (!response.ok) {
          throw new Error(`${selectedGraphFile} unavailable (${response.status})`);
        }
        const parsed = await response.json();
        let declParsed = {};
        try {
          const declResponse = await fetch(`${selectedGraphFile.replace(/\.json$/, '.decls.json')}?v=${loadNonceRef.current}`);
          if (declResponse.ok) {
            declParsed = await declResponse.json();
          }
        } catch (_) {
          // declaration metadata is optional
        }
        if (cancelled) return;
        setData(parsed);
        setDeclInfo(declParsed);
        setCustomData(null);
        setSelectedNode(null);
        setHighlightScope(null);
        setRestrictScope(null);
        setSearchScopeFilter(null);
        setGraphLoadError("");
      } catch (err) {
        if (cancelled) return;
        setData(EMPTY_DATA);
        setDeclInfo({});
        setCustomData(null);
        setGraphLoadError(err.message);
      }
    };
    loadGraph();
    return () => {
      cancelled = true;
    };
  }, [selectedGraphFile]);

  const nodeDistances = useMemo(() => distancesFromRoots(rawData), [rawData]);
  const nodeDepCounts = useMemo(() => {
    const adj = buildAdj(rawData.nodes, rawData.edges);
    const counts = {};
    for (const n of rawData.nodes) counts[n.id] = (adj[n.id] || []).length;
    return counts;
  }, [rawData]);

  const filteredNodes = useMemo(() => {
    let nodes = activeData.nodes || [];
    if (nodeSearchQuery) {
      const query = nodeSearchQuery.toLowerCase();
      nodes = nodes.filter(n => n.id.toLowerCase().includes(query));
    }
    if (searchKindFilter) {
      nodes = nodes.filter(n => nodeSemanticKind(n) === searchKindFilter);
    }
    if (searchScopeFilter !== null) {
      nodes = nodes.filter(n => scopeKeyForNode(n) === searchScopeFilter);
    }
    nodes = [...nodes].sort((a, b) => {
      if (searchSort === 'name') return a.id.localeCompare(b.id);
      if (searchSort === 'distance') return (nodeDistances[a.id] ?? Infinity) - (nodeDistances[b.id] ?? Infinity);
      if (searchSort === 'deps') return (nodeDepCounts[b.id] || 0) - (nodeDepCounts[a.id] || 0);
      return 0;
    });
    return nodes;
  }, [activeData.nodes, nodeSearchQuery, searchKindFilter, searchScopeFilter, searchSort, nodeDistances, nodeDepCounts]);

  const renderedData = useMemo(() => {
    if (!collapseNamespaces) return activeData;
    return buildNamespaceClusters(activeData);
  }, [activeData, collapseNamespaces]);

  const handleSearchKeyNav = useCallback((e) => {
    if (e.key === 'ArrowDown') {
      e.preventDefault();
      setFocusedSearchIndex(i => Math.min(i + 1, filteredNodes.length - 1));
    } else if (e.key === 'ArrowUp') {
      e.preventDefault();
      setFocusedSearchIndex(i => Math.max(i - 1, 0));
    } else if (e.key === 'Enter' && filteredNodes[focusedSearchIndex]) {
      setSelectedNode(filteredNodes[focusedSearchIndex].id);
    }
  }, [filteredNodes, focusedSearchIndex]);

  useEffect(() => { setFocusedSearchIndex(0); }, [nodeSearchQuery, searchKindFilter, searchScopeFilter]);

  const [copiedNodeId, setCopiedNodeId] = useState(false);
  const [pathStartNode, setPathStartNode] = useState(null);
  const [pathEndNode, setPathEndNode] = useState(null);
  const [allPaths, setAllPaths] = useState([]);
  const [selectedPathIndex, setSelectedPathIndex] = useState(0);

  const highlightedPath = useMemo(() => {
    if (allPaths.length === 0 || selectedPathIndex >= allPaths.length) return null;
    return allPaths[selectedPathIndex];
  }, [allPaths, selectedPathIndex]);

  const handlePathTrace = useCallback(() => {
    if (!pathStartNode || !pathEndNode) return;
    const paths = findAllPaths(activeData, pathStartNode, pathEndNode, 10, 20);
    setAllPaths(paths);
    setSelectedPathIndex(0);
  }, [activeData, pathStartNode, pathEndNode]);

  const clearPathTrace = useCallback(() => {
    setPathStartNode(null);
    setPathEndNode(null);
    setAllPaths([]);
    setSelectedPathIndex(0);
  }, []);

  const [showProofExplorer, setShowProofExplorer] = useState(false);
  const [proofPaths, setProofPaths] = useState([]);
  const [proofFilterAxiom, setProofFilterAxiom] = useState('');
  const [proofFilterTheorem, setProofFilterTheorem] = useState('');
  const [proofMaxLength, setProofMaxLength] = useState(10);
  const [selectedProofPath, setSelectedProofPath] = useState(null);

  const axiomsList = useMemo(() => 
    rawData?.nodes?.filter(n => n.kind === 'axiom').map(n => n.id) || [], 
    [rawData]
  );
  
  const theoremsList = useMemo(() => 
    rawData?.nodes?.filter(n => n.kind === 'theorem' && n.paper === -1).map(n => n.id) || [], 
    [rawData]
  );

  const computeProofPaths = useCallback(() => {
    if (!rawData) return;
    const axioms = axiomsList.filter(a => !proofFilterAxiom || a.includes(proofFilterAxiom));
    const theorems = theoremsList.filter(t => !proofFilterTheorem || t.includes(proofFilterTheorem));
    const paths = [];
    
    for (const theorem of theorems.slice(0, 20)) {
      for (const axiom of axioms.slice(0, 10)) {
        const foundPaths = findAllPaths(rawData, theorem, axiom, 3, proofMaxLength);
        for (const path of foundPaths) {
          paths.push({ theorem, axiom, path, length: path.length - 1 });
        }
      }
      if (paths.length >= 50) break;
    }
    
    setProofPaths(paths.sort((a, b) => a.length - b.length).slice(0, 50));
  }, [rawData, axiomsList, theoremsList, proofFilterAxiom, proofFilterTheorem, proofMaxLength]);

  const handleSelectProofPath = useCallback((pp) => {
    setSelectedProofPath(pp);
    setAllPaths([pp.path]);
    setSelectedPathIndex(0);
    setPathStartNode(pp.theorem);
    setPathEndNode(pp.axiom);
  }, []);

  const nodeDetails = useMemo(() => {
    if (!selectedNode || !rawData) return null;
    const node = rawData.nodes.find(n => n.id === selectedNode);
    if (!node) return null;
    const decl = declInfo[selectedNode] || null;
    const mergedNode = decl ? { ...node, ...decl } : node;

    const adj = buildAdj(rawData.nodes, rawData.edges);
    const revAdj = {};
    for (const n of rawData.nodes) revAdj[n.id] = [];
    for (const e of rawData.edges) {
      const s = typeof e.source === 'object' ? e.source.id : e.source;
      const t = typeof e.target === 'object' ? e.target.id : e.target;
      if (revAdj[t]) revAdj[t].push(s);
    }

    const dependencies = (adj[selectedNode] || []).filter(id => !isArtifact(id));
    const dependents = (revAdj[selectedNode] || []).filter(id => !isArtifact(id));

    const distanceFromCore = nodeDistances[selectedNode];

    const axiomIds = new Set(rawData.nodes.filter(n => n.kind === 'axiom').map(n => n.id));
    const witnessPath = shortestPath(adj, selectedNode, axiomIds);
    const hasPathToAxiom = witnessPath !== null;
    const reachableAxioms = [];
    const visited = new Set();
    const queue = [selectedNode];
    while (queue.length) {
      const curr = queue.shift();
      if (visited.has(curr)) continue;
      visited.add(curr);
      if (axiomIds.has(curr)) {
        reachableAxioms.push(curr);
      }
      for (const dep of adj[curr] || []) {
        if (!visited.has(dep)) queue.push(dep);
      }
    }
    const reachableFoundationAxioms = reachableAxioms.filter((id) => id.startsWith('FOUNDATION.'));
    const witnessFoundationAxioms = witnessPath
      ? witnessPath.filter((id) => id.startsWith('FOUNDATION.'))
      : [];
    const witnessAxiom = witnessPath ? witnessPath[witnessPath.length - 1] : null;

    return {
      node,
      mergedNode,
      decl,
      dependencies,
      dependents,
      distanceFromCore,
      hasPathToAxiom,
      witnessPath: witnessPath || [],
      witnessAxiom,
      witnessFoundationAxioms,
      reachableFoundationAxioms,
      signatureText: formatLeanSignature(mergedNode.signature, 800),
      signatureLatex: extractLatex(mergedNode),
      docText: decl?.doc || null,
    };
  }, [selectedNode, rawData, nodeDistances, declInfo]);
  // True Path Enforcement state
  const [showTruePaths, setShowTruePaths] = useState(false);
  const [excludeTrivialCycles, setExcludeTrivialCycles] = useState(false);
  const [truePathValidation, setTruePathValidation] = useState(null);

  // Compute true path validation on data change
  useEffect(() => {
    if (rawData?.nodes?.length > 0) {
      const validation = validateTruePaths(rawData);
      setTruePathValidation(validation);
    }
  }, [rawData]);

  // Build active filter list and apply them deterministically
  useEffect(() => {
    const f = [];
    if (viewMode === 'forcing') {
      f.push({ name: 'forcingChain' });
    } else if (viewMode === 'claims') {
      f.push({ name: 'claimsOnly' });
    } else {
      if (hideArtifacts) f.push({ name: 'hideArtifacts' });
    }
    if (depthLimit != null && depthLimit !== "") f.push({ name: 'depthLimit', params: { depth: Number(depthLimit) } });
    // Exact axiom-path filters
    if (showTruePaths) f.push({ name: 'truePathsOnly' });
    if (excludeTrivialCycles) f.push({ name: 'excludeTrivialCycles' });
    setActiveFilters(f);
  }, [viewMode, hideArtifacts, depthLimit, showTruePaths, excludeTrivialCycles]);

  const handleLoadJson = useCallback(() => {
    try {
      const parsed = JSON.parse(jsonInput);
      setCustomData(parsed);
    } catch {
      // silent
    }
  }, [jsonInput]);

  const handleMergeGraphs = useCallback(() => {
    try {
      const base = customData || JSON.parse(jsonInput || "null") || data;
      const extra = JSON.parse(additionalJson);
      const nodeMap = new Map();
      for (const n of base.nodes || []) nodeMap.set(n.id, n);
      for (const n of extra.nodes || []) nodeMap.set(n.id, { ...(nodeMap.get(n.id) || {}), ...n });
      const edgesSet = new Set();
      const edges = [];
      const addEdge = (e) => {
        const s = typeof e.source === 'object' ? e.source.id : e.source;
        const t = typeof e.target === 'object' ? e.target.id : e.target;
        const key = `${s}->${t}`;
        if (!edgesSet.has(key)) { edgesSet.add(key); edges.push({ source: s, target: t }); }
      };
      for (const e of base.edges || []) addEdge(e);
      for (const e of extra.edges || []) addEdge(e);
      const merged = { nodes: Array.from(nodeMap.values()), edges };
      setCustomData(merged);
    } catch (err) {
      // ignore parse errors for now
      console.error('merge error', err);
    }
  }, [customData, jsonInput, additionalJson, data]);

  const handleTrace = useCallback(() => {
    try {
      const adj = buildAdj(activeData.nodes, activeData.edges);
      const roots = findRoots(activeData.nodes, adj);
      const path = bfs(traceNode, adj, roots);
      setTracePath(path);
    } catch (e) {
      setTracePath([`error: ${e.message}`]);
    }
  }, [activeData, traceNode]);

  const selectConcreteNode = useCallback((nodeId) => {
    if (!nodeId) return;
    if (collapseNamespaces) setCollapseNamespaces(false);
    setSelectedNode(nodeId);
  }, [collapseNamespaces]);

  const handleGraphNodeSelect = useCallback((node) => {
    if (!node) return;
    if (node.cluster) {
      setCollapseNamespaces(false);
      setHighlightScope(node.clusterKey === "FOUNDATION" ? "FOUNDATION" : (node.clusterKey.split(".")[0] || null));
      setSelectedNode(null);
      return;
    }
    selectConcreteNode(node.id);
  }, [selectConcreteNode]);

  return (
    <div
      style={{
        fontFamily: "'JetBrains Mono', 'SF Mono', 'Fira Code', monospace",
        background: "#0a0a0a",
        color: "#e0e0e0",
        minHeight: "100vh",
        padding: 0,
        margin: 0,
      }}
    >
      {/* Header */}
      <div
        style={{
          borderBottom: "1px solid #1a1a1a",
          padding: "20px 28px",
          display: "flex",
          alignItems: "baseline",
          gap: 16,
        }}
      >
        <span
          style={{
            fontSize: 15,
            fontWeight: 700,
            letterSpacing: "0.08em",
            color: "#fff",
          }}
        >
          PROOF INTEGRITY GRAPH
        </span>
        <span style={{ fontSize: 11, color: "#555", letterSpacing: "0.05em" }}>
          ONE LOGIC GRAPH · ZERO EXITS
        </span>
      </div>

      {/* Controls */}
      <div style={{ padding: "12px 28px", borderBottom: "1px solid #1a1a1a", display: 'flex', gap: 12, alignItems: 'center', flexWrap: 'wrap' }}>
        <div style={{ display: 'flex', gap: 8, alignItems: 'center' }}>
          <span style={{ fontSize: 10, color: '#666', letterSpacing: '0.1em' }}>GRAPH</span>
          <select
            value={selectedGraphFile}
            onChange={(e) => setSelectedGraphFile(e.target.value)}
            style={{
              minWidth: 180,
              background: '#0d0d0d',
              border: '1px solid #222',
              color: '#ddd',
              padding: '6px 8px',
              borderRadius: 4,
            }}
          >
            {availableGraphs.length === 0 ? (
              <option value="">No graphs available</option>
            ) : (
              availableGraphs.map((entry) => (
                <option key={entry.file} value={entry.file}>
                  {entry.label}
                </option>
              ))
            )}
          </select>
        </div>

        {/* View Mode Toggle */}
        <div style={{ display: 'flex', gap: 4, background: '#0d0d0d', padding: 4, borderRadius: 4, border: '1px solid #222' }}>
          <button
            onClick={() => setViewMode('forcing')}
            style={{
              padding: '6px 12px',
              background: viewMode === 'forcing' ? '#2563eb' : 'transparent',
              color: viewMode === 'forcing' ? '#fff' : '#888',
              border: 'none',
              borderRadius: 3,
              fontSize: 11,
              fontWeight: viewMode === 'forcing' ? 600 : 400,
              cursor: 'pointer',
              letterSpacing: '0.03em',
            }}
          >
            FORCING CHAIN
          </button>
          <button
            onClick={() => setViewMode('claims')}
            style={{
              padding: '6px 12px',
              background: viewMode === 'claims' ? '#10b981' : 'transparent',
              color: viewMode === 'claims' ? '#000' : '#888',
              border: 'none',
              borderRadius: 3,
              fontSize: 11,
              fontWeight: viewMode === 'claims' ? 600 : 400,
              cursor: 'pointer',
              letterSpacing: '0.03em',
            }}
          >
            CLAIMS ONLY
          </button>
          <button
            onClick={() => setViewMode('full')}
            style={{
              padding: '6px 12px',
              background: viewMode === 'full' ? '#f59e0b' : 'transparent',
              color: viewMode === 'full' ? '#000' : '#888',
              border: 'none',
              borderRadius: 3,
              fontSize: 11,
              fontWeight: viewMode === 'full' ? 600 : 400,
              cursor: 'pointer',
              letterSpacing: '0.03em',
            }}
          >
            FULL GRAPH
          </button>
        </div>
        
        {viewMode === 'full' && (
          <label style={{ fontSize: 12, color: '#ccc' }}>
            <input type="checkbox" checked={hideArtifacts} onChange={(e) => setHideArtifacts(e.target.checked)} /> Hide artifacts
          </label>
        )}
        <label style={{ fontSize: 12, color: '#ccc' }}>
          <input type="checkbox" checked={collapseNamespaces} onChange={(e) => setCollapseNamespaces(e.target.checked)} /> Collapse namespaces
        </label>
        {/* Restrict-to-paper and depth controls */}
        <button
          onClick={() => setRestrictScope(restrictScope === highlightScope ? null : highlightScope)}
          title="Restrict view to currently highlighted namespace scope"
          style={{ padding: '6px 10px', marginLeft: 6, fontSize: 11, cursor: 'pointer' }}
        >
          {restrictScope == null
            ? 'Restrict to highlighted scope'
            : `Restricted: ${scopeLabelMap[restrictScope] || restrictScope}`}
        </button>
        <div style={{ display: 'flex', gap: 6, alignItems: 'center' }}>
          <input
            type="number"
            placeholder="depth"
            value={depthLimit == null ? '' : depthLimit}
            onChange={(e) => setDepthLimit(e.target.value)}
            style={{ width: 64, background:'#0d0d0d', border:'1px solid #222', color:'#ddd', padding:'6px 8px' }}
          />
          <button onClick={() => setDepthLimit(null)} style={{ padding:'6px 8px' }}>Clear depth</button>
        </div>
        
        <div style={{ display: 'flex', gap: 8, alignItems: 'center' }}>
          <input placeholder="node id to trace" value={traceNode} onChange={(e) => setTraceNode(e.target.value)}
            style={{ background:'#0d0d0d', border:'1px solid #222', color:'#ddd', padding:'6px 8px' }} />
          <button onClick={handleTrace} style={{ padding:'6px 10px' }}>Trace</button>
        </div>

        <button
          onClick={() => setShowAuditPanel(!showAuditPanel)}
          style={{ 
            padding: '6px 10px', 
            background: showAuditPanel ? '#8b5cf6' : '#1a1a1a', 
            border: '1px solid #333', 
            color: showAuditPanel ? '#fff' : '#888',
            fontSize: 11, 
            cursor: 'pointer',
            borderRadius: 4,
          }}
        >
          {showAuditPanel ? '▼ Audit' : '▶ Audit'}
        </button>

        <div style={{ marginLeft: 'auto', fontSize: 12, color: graphLoadError ? '#94a3b8' : '#888' }}>
          {graphLoadError || (stats ? `${stats.totalNodes} nodes · ${stats.totalEdges} edges` : '')}
        </div>
      </div>

      {/* Exact Axiom-Path Controls */}
      <div style={{ padding: "8px 28px", borderBottom: "1px solid #1a1a1a", display: "flex", gap: 16, alignItems: "center", background: "#0d0d15" }}>
        <span style={{ fontSize: 10, color: '#666', letterSpacing: '0.1em' }}>AXIOM PATHS:</span>
        <label style={{ fontSize: 12, color: '#ccc', cursor: 'pointer' }}>
          <input type="checkbox" checked={showTruePaths} onChange={(e) => setShowTruePaths(e.target.checked)} style={{ marginRight: 4 }} />
          Show Axiom Paths Only
        </label>
        <label style={{ fontSize: 12, color: '#ccc', cursor: 'pointer' }}>
          <input type="checkbox" checked={excludeTrivialCycles} onChange={(e) => setExcludeTrivialCycles(e.target.checked)} style={{ marginRight: 4 }} />
          Exclude Trivial Cycles
        </label>
        {truePathValidation && (
          <span style={{
            marginLeft: 'auto',
            fontSize: 11,
            color: truePathValidation.valid ? '#10b981' : '#94a3b8',
            fontWeight: 500
          }}>
            {truePathValidation.valid ? '✓' : '✗'} {truePathValidation.pathCount}/{truePathValidation.claimCount} paths ·
            {truePathValidation.cycles?.length || 0} cycles
          </span>
        )}
      </div>

      {/* View Mode Explanation */}
      <div style={{ padding: "10px 28px", borderBottom: "1px solid #1a1a1a", background: viewMode === 'forcing' ? '#0f172a' : viewMode === 'claims' ? '#0d291e' : '#291f0d' }}>
        <div style={{ fontSize: 11, color: viewMode === 'forcing' ? '#60a5fa' : viewMode === 'claims' ? '#10b981' : '#f59e0b', letterSpacing: '0.03em' }}>
          {viewMode === 'forcing' ? (
            <>
              <strong>FORCING CHAIN:</strong> Shows only the path from claims to first principles.
              Fill color shows declaration kind; outline color shows namespace scope.
              Foundation axioms are amber, local axioms are slate, definitions are violet, theorems are blue.
            </>
          ) : viewMode === 'claims' ? (
            <>
              <strong>CLAIMS ONLY MODE:</strong> Shows only theorems and definitions cited in the paper, connected through the proof structure. 
              Hides auxiliary lemmas and Lean-generated artifacts that are implementation details.
            </>
          ) : (
            <>
              <strong>FULL GRAPH MODE:</strong> Shows all nodes including auxiliary lemmas and technical infrastructure. 
              Disconnected clusters are internal proof machinery not cited in the paper text.
            </>
          )}
        </div>
      </div>

      {/* Stats row */}
      {stats && (
        <div
          style={{
            display: "grid",
            gridTemplateColumns: "repeat(4, 1fr)",
            borderBottom: "1px solid #1a1a1a",
          }}
        >
          {[
            {
              label: viewMode === 'claims' ? "PROOF STRUCTURE" : "CONNECTED COMPONENTS",
              value: stats.components,
              target: 1,
              color: stats.components === 1 ? "#10b981" : "#94a3b8",
              subtext: viewMode === 'claims'
                ? (stats.components === 1 ? "✓ UNIFIED" : "✗ FRAGMENTED")
                : (stats.components === 1 ? "✓ VERIFIED" : "✗ DISCONNECTED"),
            },
            {
              label: viewMode === 'claims' ? "UNREACHABLE CLAIMS" : "UNREACHABLE NODES",
              value: stats.orphans,
              target: 0,
              color: stats.orphans === 0 ? "#10b981" : "#94a3b8",
              subtext: stats.orphans === 0 ? "✓ ALL CONNECTED" : "✗ DISCONNECTED NODES",
            },
            {
              label: "SORRY COUNT",
              value: 0,
              target: 0,
              color: "#10b981",
              subtext: "✓ COMPLETE",
            },
            {
              label: viewMode === 'claims' ? "CITED CLAIMS" : "DECLARATIONS",
              value: stats.totalNodes,
              target: null,
              color: "#3b82f6",
              subtext: viewMode === 'claims' ? "IN PAPER" : "TOTAL",
            },
          ].map((s, i) => (
            <div
              key={i}
              style={{
                padding: "18px 28px",
                borderRight: i < 3 ? "1px solid #1a1a1a" : "none",
              }}
            >
              <div
                style={{
                  fontSize: 36,
                  fontWeight: 800,
                  color: s.color,
                  lineHeight: 1,
                  fontVariantNumeric: "tabular-nums",
                }}
              >
                {s.value}
              </div>
              <div
                style={{
                  fontSize: 9,
                  color: "#555",
                  letterSpacing: "0.12em",
                  marginTop: 6,
                }}
              >
                {s.label}
              </div>
              {s.subtext && (
                <div
                  style={{
                    fontSize: 9,
                    color: s.color,
                    marginTop: 2,
                  }}
                >
                  {s.subtext}
                </div>
              )}
            </div>
          ))}
        </div>
      )}

      {/* Breakdown row */}
      {stats && (
        <div
          style={{
            display: "flex",
            gap: 24,
            padding: "12px 28px",
            borderBottom: "1px solid #1a1a1a",
            fontSize: 11,
            color: "#666",
          }}
        >
          <span>
            theorems:{" "}
            <span style={{ color: NODE_KIND_COLORS.theorem }}>{activeNodeKindCounts.theorem}</span>
          </span>
          <span>
            definitions:{" "}
            <span style={{ color: NODE_KIND_COLORS.definition }}>{activeNodeKindCounts.definition}</span>
          </span>
          <span>
            local axioms:{" "}
            <span style={{ color: NODE_KIND_COLORS.localAxiom }}>{activeNodeKindCounts.localAxiom}</span>
          </span>
          <span>
            foundation axioms:{" "}
            <span style={{ color: NODE_KIND_COLORS.foundationAxiom }}>{activeNodeKindCounts.foundationAxiom}</span>
          </span>
          <span>
            edges:{" "}
            <span style={{ color: "#e0e0e0" }}>{stats.totalEdges}</span>
          </span>
          <span>
            reachable from ℕ:{" "}
            <span style={{ color: "#10b981" }}>{stats.reachableFromCore}</span>
            <span style={{ color: "#555" }}>/{stats.totalNodes}</span>
          </span>
        </div>
      )}

      {/* Legend */}
      <div
        style={{
          display: "flex",
          gap: 12,
          padding: "10px 28px",
          borderBottom: "1px solid #1a1a1a",
          flexWrap: "wrap",
          alignItems: "center",
        }}
      >
        <span style={{ fontSize: 10, color: "#666", letterSpacing: "0.1em" }}>KIND</span>
        {[
          ["theorem", "Theorem"],
          ["definition", "Definition"],
          ["localAxiom", "Local axiom"],
          ["foundationAxiom", "Foundation axiom"],
        ].map(([key, label]) => (
          <span
            key={key}
            style={{
              display: "inline-flex",
              alignItems: "center",
              gap: 6,
              fontSize: 10,
              color: "#aaa",
            }}
          >
            <span
              style={{
                width: 10,
                height: 10,
                borderRadius: "50%",
                display: "inline-block",
                background: NODE_KIND_COLORS[key],
                border: `1px solid ${key === "foundationAxiom" ? NODE_KIND_COLORS.foundationAxiom : "#111"}`,
              }}
            />
            {label}
          </span>
        ))}
        <span style={{ fontSize: 10, color: "#666", letterSpacing: "0.1em", marginLeft: 8 }}>SCOPE</span>
        {scopeMeta.entries.map((entry) => (
          <button
            key={entry.key}
            onClick={() =>
              setHighlightScope(
                highlightScope === entry.key ? null : entry.key
              )
            }
            style={{
              background:
                highlightScope === entry.key
                  ? entry.color + "20"
                  : "transparent",
              border: `1px solid ${
                highlightScope === entry.key ? entry.color : "#222"
              }`,
              borderRadius: 4,
              padding: "4px 10px",
              cursor: "pointer",
              display: "flex",
              alignItems: "center",
              gap: 6,
              fontSize: 10,
              color:
                highlightScope === entry.key ? entry.color : "#888",
              transition: "all 0.15s",
            }}
          >
            <span
              style={{
                width: 8,
                height: 8,
                borderRadius: "50%",
                background: "#0a0a0a",
                border: `2px solid ${entry.color}`,
                display: "inline-block",
              }}
            />
            {entry.label}
          </button>
        ))}
      </div>

      {/* Graph + Sidebar */}
      <div style={{ display: 'flex', padding: "0 28px", gap: 16 }}>
        {/* Node Search Panel */}
        <div style={{ width: 260, borderRight: '1px solid #1a1a1a', paddingRight: 16 }}>
          <div style={{ fontSize: 10, color: '#666', letterSpacing: '0.1em', marginBottom: 8 }}>
            NODES
          </div>
          <input
            ref={searchInputRef}
            type="text"
            placeholder="Search nodes..."
            value={nodeSearchQuery}
            onChange={(e) => setNodeSearchQuery(e.target.value)}
            onKeyDown={handleSearchKeyNav}
            style={{
              width: '100%',
              background: '#0d0d0d',
              border: '1px solid #222',
              borderRadius: 4,
              color: '#ddd',
              padding: '6px 8px',
              fontSize: 11,
              marginBottom: 6,
              fontFamily: 'inherit'
            }}
          />
          <div style={{ display: 'flex', gap: 4, marginBottom: 6, flexWrap: 'wrap' }}>
            <select 
              value={searchKindFilter || ''} 
              onChange={(e) => setSearchKindFilter(e.target.value || null)}
              style={{ background: '#0d0d0d', border: '1px solid #222', color: '#888', fontSize: 9, padding: '2px 4px', borderRadius: 3 }}
            >
              <option value="">All kinds</option>
              <option value="theorem">theorem</option>
              <option value="definition">definition</option>
              <option value="localAxiom">local axiom</option>
              <option value="foundationAxiom">foundation axiom</option>
            </select>
            <select 
              value={searchScopeFilter === null ? '' : searchScopeFilter} 
              onChange={(e) => setSearchScopeFilter(e.target.value === '' ? null : e.target.value)}
              style={{ background: '#0d0d0d', border: '1px solid #222', color: '#888', fontSize: 9, padding: '2px 4px', borderRadius: 3 }}
            >
              <option value="">All scopes</option>
              {scopeMeta.entries.map((entry) => (
                <option key={entry.key} value={entry.key}>{entry.label}</option>
              ))}
            </select>
            <select 
              value={searchSort} 
              onChange={(e) => setSearchSort(e.target.value)}
              style={{ background: '#0d0d0d', border: '1px solid #222', color: '#888', fontSize: 9, padding: '2px 4px', borderRadius: 3 }}
            >
              <option value="name">by name</option>
              <option value="distance">by distance</option>
              <option value="deps">by deps</option>
            </select>
          </div>
          <div style={{ fontSize: 9, color: '#555', marginBottom: 4 }}>{filteredNodes.length} nodes</div>
          <div style={{ maxHeight: 380, overflow: 'auto' }}>
            {filteredNodes.slice(0, 200).map((n, i) => (
              <div
                key={n.id}
                onClick={() => selectConcreteNode(n.id)}
                style={{
                  padding: '4px 6px',
                  fontSize: 10,
                  color: selectedNode === n.id ? '#fff' : '#888',
                  background: selectedNode === n.id ? nodeFillColor(n) + '30' : focusedSearchIndex === i ? '#1a1a1a' : 'transparent',
                  borderRadius: 3,
                  cursor: 'pointer',
                  marginBottom: 1,
                  display: 'flex',
                  alignItems: 'center',
                  gap: 6
                }}
              >
                <span style={{
                  width: 6,
                  height: 6,
                  borderRadius: '50%',
                  background: nodeFillColor(n),
                  border: `1px solid ${scopeMeta.colors[scopeKeyForNode(n)] || '#666'}`,
                  display: 'inline-block'
                }} />
                <span style={{ overflow: 'hidden', textOverflow: 'ellipsis', whiteSpace: 'nowrap', flex: 1 }}>
                  {n.id}
                </span>
                <span style={{ fontSize: 8, color: '#555' }}>{nodeSemanticKind(n)}</span>
              </div>
            ))}
            {filteredNodes.length > 200 && <div style={{ fontSize: 9, color: '#555', padding: 4 }}>+{filteredNodes.length - 200} more</div>}
          </div>
        </div>

        <div style={{ flex: 1 }}>
          <ForceGraph
            data={renderedData}
            width={700}
            height={500}
            highlightScope={highlightScope}
            scopeColors={scopeMeta.colors}
            selectedNode={selectedNode}
            onSelectNode={handleGraphNodeSelect}
            highlightedPath={highlightedPath}
          />
        </div>
        
        {/* Node Details Panel / Rejection Cost Sidebar */}
        <div style={{ width: 240, paddingLeft: 16, borderLeft: '1px solid #1a1a1a', overflowY: 'auto', maxHeight: 500 }}>
          {nodeDetails ? (
            <>
              <div style={{ fontSize: 10, color: '#666', letterSpacing: '0.1em', marginBottom: 8 }}>
                NODE DETAILS
              </div>
              
              {/* Node ID with copy */}
              <div style={{ marginBottom: 12 }}>
                <div style={{ display: 'flex', alignItems: 'center', gap: 6, marginBottom: 4 }}>
                  <span style={{
                    fontSize: 10,
                    padding: '2px 6px',
                    borderRadius: 3,
                    background: nodeFillColor(nodeDetails.node),
                    color: '#fff',
                    fontWeight: 600,
                  }}>
                    {nodeSemanticKind(nodeDetails.node).toUpperCase()}
                  </span>
                  <span style={{ fontSize: 10, color: scopeMeta.colors[scopeKeyForNode(nodeDetails.node)] || '#888' }}>
                    {scopeLabelMap[scopeKeyForNode(nodeDetails.node)] || scopeKeyForNode(nodeDetails.node)}
                  </span>
                </div>
                <div 
                  onClick={() => {
                    navigator.clipboard?.writeText(nodeDetails.node.id);
                    setCopiedNodeId(true);
                    setTimeout(() => setCopiedNodeId(false), 1500);
                  }}
                  style={{
                    fontSize: 9,
                    color: '#888',
                    background: '#0d0d0d',
                    padding: '4px 6px',
                    borderRadius: 3,
                    cursor: 'pointer',
                    wordBreak: 'break-all',
                    border: '1px solid #222',
                  }}
                >
                  {nodeDetails.node.id}
                  <span style={{ marginLeft: 6, color: copiedNodeId ? '#10b981' : '#555' }}>
                    {copiedNodeId ? '✓ copied' : '[copy]'}
                  </span>
                </div>
              </div>

              {/* Exact Axiom Path Status */}
              <div style={{ marginBottom: 12, padding: 8, background: nodeDetails.hasPathToAxiom ? '#0d1a0d' : '#0f172a', borderRadius: 4, border: `1px solid ${nodeDetails.hasPathToAxiom ? '#1a3311' : '#334155'}` }}>
                <div style={{ fontSize: 10, color: nodeDetails.hasPathToAxiom ? '#10b981' : '#94a3b8', fontWeight: 600 }}>
                  {nodeDetails.hasPathToAxiom ? '✓ PATH TO AXIOM' : '✗ NO PATH TO AXIOM'}
                </div>
                {nodeDetails.witnessAxiom && (
                  <div style={{ fontSize: 9, color: '#94a3b8', marginTop: 2, wordBreak: 'break-word' }}>
                    shortest witness ends at {nodeDetails.witnessAxiom}
                  </div>
                )}
              </div>

              {/* Distance */}
              {nodeDetails.distanceFromCore !== undefined && (
                <div style={{ marginBottom: 12 }}>
                  <div style={{ fontSize: 9, color: '#555', marginBottom: 2 }}>DISTANCE FROM ℕ</div>
                  <div style={{ fontSize: 16, color: '#3b82f6', fontWeight: 700 }}>
                    {nodeDetails.distanceFromCore}
                  </div>
                </div>
              )}

              {nodeDetails.signatureText && (
                <div style={{ marginBottom: 12 }}>
                  <div style={{ fontSize: 9, color: '#555', marginBottom: 4 }}>SIGNATURE</div>
                  <div style={{ fontSize: 11, color: '#ddd', lineHeight: 1.5, background: '#0d0d0d', border: '1px solid #222', borderRadius: 4, padding: 8 }}>
                    <LatexBlock latex={nodeDetails.signatureLatex} fallback={nodeDetails.signatureText} />
                  </div>
                  <pre style={{ marginTop: 6, whiteSpace: 'pre-wrap', wordBreak: 'break-word', fontSize: 9, color: '#94a3b8', background: '#0d0d0d', border: '1px solid #1a1a1a', borderRadius: 4, padding: 8 }}>
                    {nodeDetails.signatureText}
                  </pre>
                </div>
              )}

              {nodeDetails.docText && (
                <div style={{ marginBottom: 12 }}>
                  <div style={{ fontSize: 9, color: '#555', marginBottom: 4 }}>DOCSTRING</div>
                  <div style={{ fontSize: 10, color: '#ccc', lineHeight: 1.5, background: '#0d0d0d', border: '1px solid #222', borderRadius: 4, padding: 8, whiteSpace: 'pre-wrap' }}>
                    {nodeDetails.docText}
                  </div>
                </div>
              )}

              {/* Exact Foundation Axioms Reached */}
              {nodeDetails.reachableFoundationAxioms.length > 0 && (
                <div style={{ marginBottom: 12 }}>
                  <div style={{ fontSize: 9, color: '#555', marginBottom: 4 }}>REACHABLE FOUNDATION AXIOMS</div>
                  {nodeDetails.reachableFoundationAxioms.map((axiomId) => {
                    const info = FOUNDATION_BUCKETS[axiomId] || { name: axiomId.split('.')[1], color: '#666', description: '' };
                    return (
                      <div key={axiomId} style={{ 
                        fontSize: 9, 
                        color: info.color, 
                        marginBottom: 2,
                        padding: '3px 6px',
                        background: info.color + '15',
                        borderRadius: 3,
                        wordBreak: 'break-word',
                      }}>
                        {info.name} <span style={{ color: '#94a3b8' }}>({axiomId})</span>
                      </div>
                    );
                  })}
                </div>
              )}

              {/* Exact witness path */}
              {nodeDetails.witnessPath.length > 0 && (
                <div style={{ marginBottom: 12 }}>
                  <div style={{ fontSize: 9, color: '#555', marginBottom: 4 }}>
                    SHORTEST WITNESS PATH ({Math.max(0, nodeDetails.witnessPath.length - 1)} edges)
                  </div>
                  <div style={{ maxHeight: 120, overflow: 'auto', background: '#0d0d0d', border: '1px solid #222', borderRadius: 4, padding: 6 }}>
                    {nodeDetails.witnessPath.map((pathNode, idx) => {
                      const isFoundationAxiom = pathNode.startsWith('FOUNDATION.');
                      const info = FOUNDATION_BUCKETS[pathNode];
                      return (
                        <div
                          key={`${pathNode}:${idx}`}
                          onClick={() => selectConcreteNode(pathNode)}
                          style={{
                            fontSize: 9,
                            color: isFoundationAxiom ? (info?.color || '#f59e0b') : '#cbd5e1',
                            cursor: 'pointer',
                            padding: '2px 4px',
                            borderRadius: 2,
                            wordBreak: 'break-word',
                          }}
                          onMouseEnter={e => e.target.style.background = '#1a1a1a'}
                          onMouseLeave={e => e.target.style.background = 'transparent'}
                        >
                          {idx + 1}. {pathNode}
                        </div>
                      );
                    })}
                  </div>
                </div>
              )}

              {/* Dependencies */}
              {nodeDetails.dependencies.length > 0 && (
                <div style={{ marginBottom: 12 }}>
                  <div style={{ fontSize: 9, color: '#555', marginBottom: 4 }}>
                    DEPENDENCIES ({nodeDetails.dependencies.length})
                  </div>
                  <div style={{ maxHeight: 80, overflow: 'auto' }}>
                    {nodeDetails.dependencies.slice(0, 10).map(dep => (
                      <div 
                        key={dep}
                        onClick={() => selectConcreteNode(dep)}
                        style={{
                          fontSize: 9,
                          color: '#888',
                          cursor: 'pointer',
                          padding: '2px 4px',
                          borderRadius: 2,
                        }}
                        onMouseEnter={e => e.target.style.background = '#1a1a1a'}
                        onMouseLeave={e => e.target.style.background = 'transparent'}
                      >
                        → {dep}
                      </div>
                    ))}
                    {nodeDetails.dependencies.length > 10 && (
                      <div style={{ fontSize: 8, color: '#555' }}>+{nodeDetails.dependencies.length - 10} more</div>
                    )}
                  </div>
                </div>
              )}

              {/* Dependents */}
              {nodeDetails.dependents.length > 0 && (
                <div style={{ marginBottom: 12 }}>
                  <div style={{ fontSize: 9, color: '#555', marginBottom: 4 }}>
                    DEPENDENTS ({nodeDetails.dependents.length})
                  </div>
                  <div style={{ maxHeight: 80, overflow: 'auto' }}>
                    {nodeDetails.dependents.slice(0, 10).map(dep => (
                      <div 
                        key={dep}
                        onClick={() => selectConcreteNode(dep)}
                        style={{
                          fontSize: 9,
                          color: '#888',
                          cursor: 'pointer',
                          padding: '2px 4px',
                          borderRadius: 2,
                        }}
                        onMouseEnter={e => e.target.style.background = '#1a1a1a'}
                        onMouseLeave={e => e.target.style.background = 'transparent'}
                      >
                        ← {dep}
                      </div>
                    ))}
                    {nodeDetails.dependents.length > 10 && (
                      <div style={{ fontSize: 8, color: '#555' }}>+{nodeDetails.dependents.length - 10} more</div>
                    )}
                  </div>
                </div>
              )}

              {/* Trace buttons */}
              <div style={{ display: 'flex', gap: 6 }}>
                <button
                  onClick={() => { setTraceNode(selectedNode); handleTrace(); }}
                  style={{
                    flex: 1,
                    padding: '6px 8px',
                    fontSize: 9,
                    background: '#1a1a1a',
                    border: '1px solid #333',
                    borderRadius: 4,
                    color: '#ccc',
                    cursor: 'pointer',
                  }}
                >
                  Trace from here
                </button>
              </div>
            </>
          ) : (
            <>
              <div style={{ fontSize: 10, color: '#666', letterSpacing: '0.1em', marginBottom: 12 }}>
                FORCING GUIDE
              </div>
              
              {viewMode === 'forcing' && (
                <>
                  <div style={{ marginBottom: 16 }}>
                    <div style={{ fontSize: 11, color: NODE_KIND_COLORS.theorem, fontWeight: 600, marginBottom: 4 }}>
                      THEOREMS
                    </div>
                    <div style={{ fontSize: 10, color: '#888', lineHeight: 1.4 }}>
                      Blue fill marks theorems in the current forcing path.
                    </div>
                  </div>
                  
                  <div style={{ marginBottom: 16 }}>
                    <div style={{ fontSize: 11, color: NODE_KIND_COLORS.foundationAxiom, fontWeight: 600, marginBottom: 4 }}>
                      FOUNDATION AXIOMS
                    </div>
                    <div style={{ fontSize: 10, color: '#888', lineHeight: 1.4 }}>
                      Amber fill marks collapsed foundational prerequisites.
                    </div>
                  </div>
                  
                  <div style={{ marginBottom: 16 }}>
                    <div style={{ fontSize: 11, color: '#94a3b8', fontWeight: 600, marginBottom: 4 }}>
                      NAMESPACE SCOPES
                    </div>
                    <div style={{ fontSize: 10, color: '#888', lineHeight: 1.4 }}>
                      Node outlines show which namespace a declaration belongs to.
                    </div>
                  </div>
                  
                </>
              )}
              
              <div style={{ fontSize: 10, color: '#555', marginTop: 12, lineHeight: 1.5 }}>
                Click a node in the graph or search panel to see details.
              </div>
            </>
          )}
        </div>
      </div>

      {/* Trace output */}
      <div style={{ padding: '8px 28px', minHeight: 36 }}>
        {tracePath && (
          <div style={{ background: '#0d0d0d', border: '1px solid #222', padding: 8, borderRadius: 4, color:'#ddd', fontSize:12 }}>
            <strong>Trace path:</strong> {tracePath.join(' → ')}
          </div>
        )}
      </div>

      {/* Path Tracer UI */}
      <div style={{ padding: '8px 28px', borderTop: '1px solid #1a1a1a' }}>
        <div style={{ fontSize: 10, color: '#666', letterSpacing: '0.1em', marginBottom: 8 }}>
          PATH TRACER
        </div>
        <div style={{ display: 'flex', gap: 8, alignItems: 'center', flexWrap: 'wrap' }}>
          <div style={{ display: 'flex', gap: 6, alignItems: 'center' }}>
            <span style={{ fontSize: 10, color: '#888' }}>From:</span>
            <input
              placeholder="Start node"
              value={pathStartNode || ''}
              onChange={(e) => setPathStartNode(e.target.value || null)}
              style={{ 
                width: 180, 
                background: '#0d0d0d', 
                border: '1px solid #222', 
                color: '#ddd', 
                padding: '6px 8px', 
                fontSize: 10,
                borderRadius: 4,
              }}
            />
          </div>
          <span style={{ color: '#555' }}>→</span>
          <div style={{ display: 'flex', gap: 6, alignItems: 'center' }}>
            <span style={{ fontSize: 10, color: '#888' }}>To:</span>
            <input
              placeholder="End node"
              value={pathEndNode || ''}
              onChange={(e) => setPathEndNode(e.target.value || null)}
              style={{ 
                width: 180, 
                background: '#0d0d0d', 
                border: '1px solid #222', 
                color: '#ddd', 
                padding: '6px 8px', 
                fontSize: 10,
                borderRadius: 4,
              }}
            />
          </div>
          <button
            onClick={handlePathTrace}
            disabled={!pathStartNode || !pathEndNode}
            style={{
              padding: '6px 12px',
              background: pathStartNode && pathEndNode ? '#3b82f6' : '#1a1a1a',
              border: '1px solid #333',
              borderRadius: 4,
              color: pathStartNode && pathEndNode ? '#fff' : '#555',
              fontSize: 10,
              cursor: pathStartNode && pathEndNode ? 'pointer' : 'not-allowed',
            }}
          >
            Find Paths
          </button>
          {(pathStartNode || pathEndNode) && (
            <button
              onClick={clearPathTrace}
              style={{
                padding: '6px 12px',
                background: '#1a1a1a',
                border: '1px solid #333',
                borderRadius: 4,
                color: '#888',
                fontSize: 10,
                cursor: 'pointer',
              }}
            >
              Clear
            </button>
          )}
        </div>
        
        {/* Path results */}
        {allPaths.length > 0 && (
          <div style={{ marginTop: 12, background: '#0d0d0d', border: '1px solid #222', borderRadius: 4, padding: 8 }}>
            <div style={{ display: 'flex', justifyContent: 'space-between', alignItems: 'center', marginBottom: 8 }}>
              <span style={{ fontSize: 10, color: '#888' }}>
                {allPaths.length} path{allPaths.length !== 1 ? 's' : ''} found
              </span>
              {allPaths.length > 1 && (
                <div style={{ display: 'flex', gap: 4 }}>
                  <button
                    onClick={() => setSelectedPathIndex(i => Math.max(0, i - 1))}
                    disabled={selectedPathIndex === 0}
                    style={{ padding: '2px 8px', fontSize: 9, background: '#1a1a1a', border: '1px solid #333', color: selectedPathIndex === 0 ? '#555' : '#ccc', cursor: selectedPathIndex === 0 ? 'not-allowed' : 'pointer' }}
                  >
                    ←
                  </button>
                  <span style={{ fontSize: 10, color: '#888' }}>{selectedPathIndex + 1}/{allPaths.length}</span>
                  <button
                    onClick={() => setSelectedPathIndex(i => Math.min(allPaths.length - 1, i + 1))}
                    disabled={selectedPathIndex === allPaths.length - 1}
                    style={{ padding: '2px 8px', fontSize: 9, background: '#1a1a1a', border: '1px solid #333', color: selectedPathIndex === allPaths.length - 1 ? '#555' : '#ccc', cursor: selectedPathIndex === allPaths.length - 1 ? 'not-allowed' : 'pointer' }}
                  >
                    →
                  </button>
                </div>
              )}
            </div>
            <div style={{ fontSize: 9, color: '#3b82f6', marginBottom: 4 }}>
              Path {selectedPathIndex + 1}: length {allPaths[selectedPathIndex]?.length - 1 || 0}
            </div>
            <div style={{ fontSize: 10, color: '#ccc', lineHeight: 1.6, wordBreak: 'break-all' }}>
              {allPaths[selectedPathIndex]?.join(' → ')}
            </div>
            {allPaths.length > 1 && (
              <div style={{ marginTop: 8, maxHeight: 80, overflow: 'auto', borderTop: '1px solid #222', paddingTop: 8 }}>
                {allPaths.map((path, i) => (
                  <div 
                    key={i}
                    onClick={() => setSelectedPathIndex(i)}
                    style={{
                      fontSize: 9,
                      color: i === selectedPathIndex ? '#3b82f6' : '#666',
                      cursor: 'pointer',
                      padding: '2px 4px',
                      background: i === selectedPathIndex ? '#1a2733' : 'transparent',
                      borderRadius: 2,
                      marginBottom: 2,
                    }}
                  >
                    Path {i + 1} (len {path.length - 1}): {path.slice(0, 3).join(' → ')}{path.length > 3 ? ' ...' : ''}
                  </div>
                ))}
              </div>
            )}
          </div>
        )}
      </div>

      {/* Proof Paths Explorer */}
      <div style={{ padding: '8px 28px', borderTop: '1px solid #1a1a1a' }}>
        <div 
          style={{ display: 'flex', justifyContent: 'space-between', alignItems: 'center', cursor: 'pointer' }}
          onClick={() => setShowProofExplorer(!showProofExplorer)}
        >
          <div style={{ fontSize: 10, color: '#666', letterSpacing: '0.1em' }}>
            PROOF PATHS EXPLORER
          </div>
          <span style={{ color: '#555', fontSize: 10 }}>{showProofExplorer ? '▼' : '▶'}</span>
        </div>
        
        {showProofExplorer && (
          <div style={{ marginTop: 12 }}>
            <div style={{ display: 'flex', gap: 8, alignItems: 'center', flexWrap: 'wrap', marginBottom: 8 }}>
              <div style={{ display: 'flex', gap: 4, alignItems: 'center' }}>
                <span style={{ fontSize: 9, color: '#888' }}>Axiom filter:</span>
                <input
                  placeholder="FOUNDATION.Counting"
                  value={proofFilterAxiom}
                  onChange={(e) => setProofFilterAxiom(e.target.value)}
                  style={{ width: 140, background: '#0d0d0d', border: '1px solid #222', color: '#ddd', padding: '4px 6px', fontSize: 9, borderRadius: 3 }}
                />
              </div>
              <div style={{ display: 'flex', gap: 4, alignItems: 'center' }}>
                <span style={{ fontSize: 9, color: '#888' }}>Theorem filter:</span>
                <input
                  placeholder="theorem name"
                  value={proofFilterTheorem}
                  onChange={(e) => setProofFilterTheorem(e.target.value)}
                  style={{ width: 140, background: '#0d0d0d', border: '1px solid #222', color: '#ddd', padding: '4px 6px', fontSize: 9, borderRadius: 3 }}
                />
              </div>
              <div style={{ display: 'flex', gap: 4, alignItems: 'center' }}>
                <span style={{ fontSize: 9, color: '#888' }}>Max length:</span>
                <input
                  type="number"
                  value={proofMaxLength}
                  onChange={(e) => setProofMaxLength(Number(e.target.value) || 10)}
                  style={{ width: 50, background: '#0d0d0d', border: '1px solid #222', color: '#ddd', padding: '4px 6px', fontSize: 9, borderRadius: 3 }}
                />
              </div>
              <button
                onClick={computeProofPaths}
                style={{
                  padding: '4px 10px',
                  background: '#3b82f6',
                  border: 'none',
                  borderRadius: 3,
                  color: '#fff',
                  fontSize: 9,
                  cursor: 'pointer',
                }}
              >
                Compute Paths
              </button>
              {proofPaths.length > 0 && (
                <button
                  onClick={() => {
                    const md = proofPaths.map(p => 
                      `## ${p.theorem} → ${p.axiom}\nLength: ${p.length}\nPath: ${p.path.join(' → ')}`
                    ).join('\n\n');
                    navigator.clipboard?.writeText(md);
                  }}
                  style={{
                    padding: '4px 10px',
                    background: '#1a1a1a',
                    border: '1px solid #333',
                    borderRadius: 3,
                    color: '#888',
                    fontSize: 9,
                    cursor: 'pointer',
                  }}
                >
                  Export MD
                </button>
              )}
            </div>
            
            {proofPaths.length > 0 && (
              <div style={{ background: '#0d0d0d', border: '1px solid #222', borderRadius: 4, maxHeight: 200, overflow: 'auto' }}>
                <div style={{ fontSize: 9, color: '#888', padding: 8, borderBottom: '1px solid #222' }}>
                  {proofPaths.length} proof paths computed
                </div>
                {proofPaths.map((pp, i) => (
                  <div 
                    key={i}
                    onClick={() => handleSelectProofPath(pp)}
                    style={{
                      padding: '6px 8px',
                      borderBottom: '1px solid #1a1a1a',
                      cursor: 'pointer',
                      background: selectedProofPath === pp ? '#1a2733' : 'transparent',
                    }}
                  >
                    <div style={{ fontSize: 9, color: '#3b82f6', marginBottom: 2 }}>
                      {pp.theorem} → {pp.axiom}
                    </div>
                    <div style={{ fontSize: 8, color: '#666' }}>
                      Length: {pp.length} | {pp.path.slice(0, 4).join(' → ')}{pp.path.length > 4 ? ' ...' : ''}
                    </div>
                  </div>
                ))}
              </div>
            )}
            
            {proofPaths.length === 0 && (
              <div style={{ fontSize: 9, color: '#555' }}>
                Click "Compute Paths" to find all paths from theorems to axioms.
              </div>
            )}
          </div>
        )}
      </div>

      {/* Audit Mode Panel */}
      <div style={{ padding: '8px 28px', borderTop: '1px solid #1a1a1a' }}>
        <div 
          style={{ display: 'flex', justifyContent: 'space-between', alignItems: 'center', cursor: 'pointer' }}
          onClick={() => setShowAuditPanel(!showAuditPanel)}
        >
          <div style={{ fontSize: 10, color: '#666', letterSpacing: '0.1em' }}>
            AUDIT MODE
          </div>
          <span style={{ color: '#555', fontSize: 10 }}>{showAuditPanel ? '▼' : '▶'}</span>
        </div>
        
        {showAuditPanel && (
          <div style={{ marginTop: 12 }}>
            {/* Exact Axiom-Path Coverage */}
            <div style={{ marginBottom: 16 }}>
              <div style={{ fontSize: 11, color: '#10b981', fontWeight: 600, marginBottom: 8 }}>
                AXIOM PATH COVERAGE
              </div>
              {truePathValidation ? (
                <div style={{ background: '#0d0d0d', border: '1px solid #222', borderRadius: 4, padding: 8 }}>
                  <div style={{ display: 'grid', gridTemplateColumns: 'repeat(4, 1fr)', gap: 12, marginBottom: 8 }}>
                    <div>
                      <div style={{ fontSize: 9, color: '#555' }}>STATUS</div>
                      <div style={{ fontSize: 12, color: truePathValidation.valid ? '#10b981' : '#94a3b8', fontWeight: 600 }}>
                        {truePathValidation.valid ? '✓ VALID' : '✗ INVALID'}
                      </div>
                    </div>
                    <div>
                      <div style={{ fontSize: 9, color: '#555' }}>CLAIMS</div>
                      <div style={{ fontSize: 12, color: '#3b82f6' }}>{truePathValidation.claimCount}</div>
                    </div>
                    <div>
                      <div style={{ fontSize: 9, color: '#555' }}>PATHS</div>
                      <div style={{ fontSize: 12, color: '#3b82f6' }}>{truePathValidation.pathCount}</div>
                    </div>
                    <div>
                      <div style={{ fontSize: 9, color: '#555' }}>CYCLES</div>
                      <div style={{ fontSize: 12, color: '#3b82f6' }}>{truePathValidation.cycles?.length || 0}</div>
                    </div>
                  </div>
                  
                  {truePathValidation.missingPaths?.length > 0 && (
                    <div style={{ marginBottom: 8 }}>
                      <div style={{ fontSize: 9, color: '#94a3b8', marginBottom: 4 }}>
                        ⚠ {truePathValidation.missingPaths.length} claims without axiom paths:
                      </div>
                      <div style={{ maxHeight: 60, overflow: 'auto' }}>
                        {truePathValidation.missingPaths.slice(0, 10).map(mp => (
                          <div key={mp} style={{ fontSize: 8, color: '#888', marginLeft: 8 }}>• {mp}</div>
                        ))}
                        {truePathValidation.missingPaths.length > 10 && (
                          <div style={{ fontSize: 8, color: '#555' }}>+{truePathValidation.missingPaths.length - 10} more</div>
                        )}
                      </div>
                    </div>
                  )}
                  
                  <div style={{ display: 'grid', gridTemplateColumns: '1fr 1fr', gap: 8 }}>
                    <div>
                      <div style={{ fontSize: 9, color: '#555' }}>NONTRIVIAL CYCLES</div>
                      <div style={{ fontSize: 11, color: '#f59e0b' }}>{truePathValidation.nontrivialCycles?.length || 0}</div>
                    </div>
                    <div>
                      <div style={{ fontSize: 9, color: '#555' }}>TRIVIAL CYCLES</div>
                      <div style={{ fontSize: 11, color: '#94a3b8' }}>{truePathValidation.trivialCycles?.length || 0} ⚠</div>
                    </div>
                  </div>
                </div>
              ) : (
                <div style={{ fontSize: 9, color: '#555' }}>No validation data available</div>
              )}
            </div>

            {/* Foundation Bucket Usage */}
            <div style={{ marginBottom: 16 }}>
              <div style={{ fontSize: 11, color: '#3b82f6', fontWeight: 600, marginBottom: 8 }}>
                FOUNDATION BUCKET COVERAGE
              </div>
              <div style={{ background: '#0d0d0d', border: '1px solid #222', borderRadius: 4, padding: 8 }}>
                {Object.entries(FOUNDATION_BUCKETS).map(([key, info]) => (
                  <div key={key} style={{ display: 'flex', alignItems: 'center', gap: 8, marginBottom: 4 }}>
                    <span style={{
                      width: 8,
                      height: 8,
                      borderRadius: '50%',
                      background: info.color,
                      display: 'inline-block',
                    }} />
                    <span style={{ fontSize: 9, color: '#888', flex: 1 }}>{info.name}</span>
                    <span style={{ fontSize: 8, color: '#555' }}>{info.description}</span>
                  </div>
                ))}
              </div>
            </div>

            {/* Cycle Analysis */}
            {truePathValidation?.cycles?.length > 0 && (
              <div style={{ marginBottom: 16 }}>
                <div style={{ fontSize: 11, color: '#f59e0b', fontWeight: 600, marginBottom: 8 }}>
                  CYCLE ANALYSIS
                </div>
                <div style={{ background: '#0d0d0d', border: '1px solid #222', borderRadius: 4, padding: 8, maxHeight: 120, overflow: 'auto' }}>
                  {truePathValidation.cycles.slice(0, 10).map((cycle, i) => (
                    <div key={i} style={{ marginBottom: 6, paddingBottom: 6, borderBottom: '1px solid #1a1a1a' }}>
                      <div style={{ display: 'flex', justifyContent: 'space-between', alignItems: 'center' }}>
                        <span style={{ fontSize: 9, color: cycle.isNontrivial ? '#f59e0b' : '#94a3b8' }}>
                          {cycle.isNontrivial ? '◆' : '○'} Cycle {i + 1} ({cycle.nodes.length} nodes)
                        </span>
                        {cycle.nontrivialityScore !== undefined && (
                          <span style={{ fontSize: 8, color: '#555' }}>score: {cycle.nontrivialityScore.toFixed(2)}</span>
                        )}
                      </div>
                      <div style={{ fontSize: 8, color: '#666', marginTop: 2 }}>
                        {cycle.nodes.slice(0, 3).join(' → ')}{cycle.nodes.length > 3 ? ' ...' : ''}
                      </div>
                    </div>
                  ))}
                </div>
              </div>
            )}

            {/* Export Report */}
            <div>
              <div style={{ fontSize: 11, color: '#8b5cf6', fontWeight: 600, marginBottom: 8 }}>
                EXPORT REPORT
              </div>
              <div style={{ display: 'flex', gap: 8 }}>
                <button
                  onClick={() => {
                    if (!truePathValidation) return;
                    const report = generateValidationReport(truePathValidation);
                    navigator.clipboard?.writeText(report);
                  }}
                  style={{
                    padding: '6px 12px',
                    background: '#1a1a1a',
                    border: '1px solid #333',
                    borderRadius: 4,
                    color: '#ccc',
                    fontSize: 9,
                    cursor: 'pointer',
                  }}
                >
                  Copy Report
                </button>
                <button
                  onClick={() => {
                    if (!rawData) return;
                    const json = JSON.stringify({
                      stats: stats,
                      validation: truePathValidation,
                      knownFoundationAxioms: Object.keys(FOUNDATION_BUCKETS),
                    }, null, 2);
                    const blob = new Blob([json], { type: 'application/json' });
                    const url = URL.createObjectURL(blob);
                    const a = document.createElement('a');
                    a.href = url;
                    a.download = 'audit-report.json';
                    a.click();
                    URL.revokeObjectURL(url);
                  }}
                  style={{
                    padding: '6px 12px',
                    background: '#1a1a1a',
                    border: '1px solid #333',
                    borderRadius: 4,
                    color: '#ccc',
                    fontSize: 9,
                    cursor: 'pointer',
                  }}
                >
                  Download JSON
                </button>
              </div>
            </div>
          </div>
        )}
      </div>

      {/* Import section */}
      <div
        style={{
          padding: "16px 28px",
          borderTop: "1px solid #1a1a1a",
        }}
      >
        <div
          style={{
            fontSize: 9,
            color: "#555",
            letterSpacing: "0.1em",
            marginBottom: 8,
          }}
        >
          LOAD GRAPH.JSON FROM{" "}
          <span style={{ color: "#888" }}>#export_graph_json</span>
        </div>
        <div style={{ display: "flex", gap: 8 }}>
          <textarea
            value={jsonInput}
            onChange={(e) => setJsonInput(e.target.value)}
            placeholder='Paste graph.json contents here...'
            style={{
              flex: 1,
              background: "#111",
              border: "1px solid #222",
              borderRadius: 4,
              color: "#888",
              fontFamily: "inherit",
              fontSize: 10,
              padding: "8px 12px",
              resize: "vertical",
              minHeight: 36,
              maxHeight: 120,
            }}
          />
          <button
            onClick={handleLoadJson}
            style={{
              background: "#1a1a1a",
              border: "1px solid #333",
              borderRadius: 4,
              color: "#e0e0e0",
              fontFamily: "inherit",
              fontSize: 10,
              padding: "8px 16px",
              cursor: "pointer",
              letterSpacing: "0.05em",
              whiteSpace: "nowrap",
            }}
          >
            LOAD
          </button>
        </div>
      </div>

      {/* Footer */}
      <div
        style={{
          padding: "16px 28px",
          borderTop: "1px solid #1a1a1a",
          fontSize: 9,
          color: "#333",
          letterSpacing: "0.05em",
        }}
      >
        {viewMode === 'forcing' ? (
          <>
            <strong style={{ color: '#60a5fa' }}>FORCING CHAIN:</strong> Every claim traces to counting (Nat) and logic (Decidable).
            The chain is visible from the current claim set to the foundational prerequisites.
          </>
        ) : (
          <>
            To reject any node in this graph, trace the dependency chain to its root.
            The root is ℕ. To reject any definition, you must reject counting.
          </>
        )}
      </div>
    </div>
  );
}
