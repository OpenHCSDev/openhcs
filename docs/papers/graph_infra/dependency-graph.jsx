import { useState, useEffect, useRef, useCallback } from "react";
import * as d3 from "d3";

// Demo data representing the structure of the 4-paper infrastructure
// Replace with actual graph.json from #export_graph_json
const DEMO_DATA = generateDemoGraph();

function generateDemoGraph() {
  const modules = [
    // Paper 1: AbstractClassSystem
    { prefix: "ACS", count: 40, kind: "theorem", paper: 1 },
    { prefix: "ACS.Def", count: 15, kind: "definition", paper: 1 },
    // Paper 2: SSOT
    { prefix: "Ssot", count: 25, kind: "theorem", paper: 2 },
    { prefix: "Ssot.Def", count: 10, kind: "definition", paper: 2 },
    // Paper 3: Leverage
    { prefix: "Leverage", count: 30, kind: "theorem", paper: 3 },
    { prefix: "Leverage.Def", count: 12, kind: "definition", paper: 3 },
    // Paper 4: DecisionQuotient
    { prefix: "DQ", count: 60, kind: "theorem", paper: 4 },
    { prefix: "DQ.Def", count: 25, kind: "definition", paper: 4 },
    { prefix: "DQ.Thermo", count: 20, kind: "theorem", paper: 4 },
    // Bridge
    { prefix: "Bridge", count: 15, kind: "theorem", paper: 0 },
    // Core
    { prefix: "Core.Nat", count: 3, kind: "axiom", paper: -1 },
  ];

  const nodes = [];
  const edges = [];
  let id = 0;

  for (const mod of modules) {
    for (let i = 0; i < mod.count; i++) {
      nodes.push({
        id: `${mod.prefix}.${i}`,
        kind: mod.kind,
        paper: mod.paper,
      });
      id++;
    }
  }

  // Create dense connectivity within modules
  for (const mod of modules) {
    const modNodes = nodes.filter((n) => n.id.startsWith(mod.prefix + "."));
    for (let i = 1; i < modNodes.length; i++) {
      edges.push({ source: modNodes[i].id, target: modNodes[i - 1].id });
      if (i > 2 && Math.random() > 0.6) {
        const j = Math.floor(Math.random() * (i - 1));
        edges.push({ source: modNodes[i].id, target: modNodes[j].id });
      }
    }
  }

  // Cross-module dependencies (papers depend on earlier papers)
  const paperNodes = (p) => nodes.filter((n) => n.paper === p);
  const connect = (fromPaper, toPaper, count) => {
    const from = paperNodes(fromPaper);
    const to = paperNodes(toPaper);
    for (let i = 0; i < count; i++) {
      const f = from[Math.floor(Math.random() * from.length)];
      const t = to[Math.floor(Math.random() * to.length)];
      edges.push({ source: f.id, target: t.id });
    }
  };

  // Core -> everything
  const core = paperNodes(-1);
  for (const p of [1, 2, 3, 4]) {
    const pn = paperNodes(p);
    for (let i = 0; i < 5; i++) {
      edges.push({
        source: pn[Math.floor(Math.random() * pn.length)].id,
        target: core[Math.floor(Math.random() * core.length)].id,
      });
    }
  }

  connect(2, 1, 12); // SSOT depends on ACS
  connect(3, 1, 8); // Leverage depends on ACS
  connect(3, 2, 10); // Leverage depends on SSOT
  connect(4, 1, 6); // DQ depends on ACS
  connect(0, 3, 8); // Bridge depends on Leverage
  connect(0, 4, 8); // Bridge depends on DQ
  connect(0, 2, 4); // Bridge depends on SSOT

  return { nodes, edges };
}

const PAPER_COLORS = {
  [-1]: "#ef4444", // Core/Nat — red
  0: "#f59e0b", // Bridge — amber
  1: "#3b82f6", // Paper 1: ACS — blue
  2: "#8b5cf6", // Paper 2: SSOT — purple
  3: "#10b981", // Paper 3: Leverage — green
  4: "#ec4899", // Paper 4: DQ — pink
};

const PAPER_NAMES = {
  [-1]: "Core Axioms (ℕ)",
  0: "Bridge Theorems",
  1: "Paper 1: AbstractClassSystem",
  2: "Paper 2: SSOT",
  3: "Paper 3: Leverage",
  4: "Paper 4: DecisionQuotient",
};

const KIND_SHAPES = {
  theorem: "circle",
  definition: "square",
  axiom: "diamond",
  other: "circle",
};

function computeStats(data) {
  const nodeSet = new Set(data.nodes.map((n) => n.id));
  const adj = {};
  for (const n of data.nodes) adj[n.id] = [];
  for (const e of data.edges) {
    if (adj[e.source]) adj[e.source].push(e.target);
    if (adj[e.target]) adj[e.target].push(e.source);
  }

  // BFS for connected components
  const visited = new Set();
  let components = 0;
  for (const n of data.nodes) {
    if (!visited.has(n.id)) {
      components++;
      const queue = [n.id];
      while (queue.length > 0) {
        const curr = queue.shift();
        if (visited.has(curr)) continue;
        visited.add(curr);
        for (const neighbor of adj[curr] || []) {
          if (!visited.has(neighbor)) queue.push(neighbor);
        }
      }
    }
  }

  // Reachability from core
  const coreNodes = data.nodes.filter((n) => n.paper === -1).map((n) => n.id);
  const reachableFromCore = new Set();
  const queue = [...coreNodes];
  // Reverse edges: who depends on core?
  const reverseAdj = {};
  for (const n of data.nodes) reverseAdj[n.id] = [];
  for (const e of data.edges) {
    if (reverseAdj[e.target]) reverseAdj[e.target].push(e.source);
  }
  while (queue.length > 0) {
    const curr = queue.shift();
    if (reachableFromCore.has(curr)) continue;
    reachableFromCore.add(curr);
    for (const dep of reverseAdj[curr] || []) {
      if (!reachableFromCore.has(dep)) queue.push(dep);
    }
  }
  // Also add nodes reachable via forward edges from core
  const fwdQueue = [...coreNodes];
  while (fwdQueue.length > 0) {
    const curr = fwdQueue.shift();
    if (reachableFromCore.has(curr)) continue;
    reachableFromCore.add(curr);
    for (const dep of adj[curr] || []) {
      if (!reachableFromCore.has(dep)) fwdQueue.push(dep);
    }
  }

  const orphans = data.nodes.filter((n) => !reachableFromCore.has(n.id));

  const theorems = data.nodes.filter((n) => n.kind === "theorem").length;
  const definitions = data.nodes.filter((n) => n.kind === "definition").length;
  const axioms = data.nodes.filter((n) => n.kind === "axiom").length;

  return {
    totalNodes: data.nodes.length,
    totalEdges: data.edges.length,
    components,
    orphans: orphans.length,
    theorems,
    definitions,
    axioms,
    reachableFromCore: reachableFromCore.size,
  };
}

function ForceGraph({ data, width, height, highlightPaper }) {
  const svgRef = useRef(null);
  const simRef = useRef(null);

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

    const sim = d3
      .forceSimulation(nodes)
      .force(
        "link",
        d3
          .forceLink(edges)
          .id((d) => d.id)
          .distance(15)
          .strength(0.3)
      )
      .force("charge", d3.forceManyBody().strength(-8).distanceMax(150))
      .force("center", d3.forceCenter(width / 2, height / 2))
      .force("collision", d3.forceCollide(4))
      .force(
        "cluster",
        d3.forceX(width / 2).strength(0.01)
      )
      .force("clusterY", d3.forceY(height / 2).strength(0.01));

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
      .attr("r", (d) => (d.kind === "axiom" ? 5 : d.kind === "definition" ? 3.5 : 2.5))
      .attr("fill", (d) => PAPER_COLORS[d.paper] || "#666")
      .attr("stroke", "none")
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

    node.append("title").text((d) => `${d.id} (${d.kind})`);

    sim.on("tick", () => {
      link
        .attr("x1", (d) => d.source.x)
        .attr("y1", (d) => d.source.y)
        .attr("x2", (d) => d.target.x)
        .attr("y2", (d) => d.target.y);
      node.attr("cx", (d) => d.x).attr("cy", (d) => d.y);
    });

    // Highlight paper on hover
    if (highlightPaper !== null) {
      node
        .attr("opacity", (d) =>
          d.paper === highlightPaper ? 1 : 0.08
        )
        .attr("r", (d) =>
          d.paper === highlightPaper
            ? d.kind === "axiom" ? 7 : d.kind === "definition" ? 5 : 4
            : d.kind === "axiom" ? 5 : d.kind === "definition" ? 3.5 : 2.5
        );
      link.attr("stroke", (d) => {
        const s = typeof d.source === "object" ? d.source : nodes.find((n) => n.id === d.source);
        const t = typeof d.target === "object" ? d.target : nodes.find((n) => n.id === d.target);
        return s?.paper === highlightPaper || t?.paper === highlightPaper
          ? PAPER_COLORS[highlightPaper] + "40"
          : "#ffffff03";
      });
    } else {
      node.attr("opacity", 0.85);
      link.attr("stroke", "#ffffff08");
    }

    return () => sim.stop();
  }, [data, width, height, highlightPaper]);

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
  const [data] = useState(DEMO_DATA);
  const [stats, setStats] = useState(null);
  const [highlightPaper, setHighlightPaper] = useState(null);
  const [jsonInput, setJsonInput] = useState("");
  const [customData, setCustomData] = useState(null);

  useEffect(() => {
    setStats(computeStats(customData || data));
  }, [data, customData]);

  const activeData = customData || data;

  const handleLoadJson = useCallback(() => {
    try {
      const parsed = JSON.parse(jsonInput);
      // Assign papers based on prefix if not present
      for (const n of parsed.nodes) {
        if (n.paper === undefined) {
          if (n.id.startsWith("AbstractClassSystem")) n.paper = 1;
          else if (n.id.startsWith("Ssot")) n.paper = 2;
          else if (n.id.startsWith("Leverage")) n.paper = 3;
          else if (n.id.startsWith("DecisionQuotient")) n.paper = 4;
          else if (n.id.includes("Nat") || n.id.includes("Core")) n.paper = -1;
          else n.paper = 0;
        }
      }
      setCustomData(parsed);
    } catch {
      // silent
    }
  }, [jsonInput]);

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
              label: "CONNECTED COMPONENTS",
              value: stats.components,
              target: 1,
              color: stats.components === 1 ? "#10b981" : "#ef4444",
            },
            {
              label: "COUNTING REJECTIONS",
              value: stats.orphans,
              target: 0,
              color: stats.orphans === 0 ? "#10b981" : "#ef4444",
            },
            {
              label: "SORRY COUNT",
              value: 0,
              target: 0,
              color: "#10b981",
            },
            {
              label: "DECLARATIONS",
              value: stats.totalNodes,
              target: null,
              color: "#3b82f6",
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
              {s.target !== null && (
                <div
                  style={{
                    fontSize: 9,
                    color: s.value === s.target ? "#10b981" : "#ef4444",
                    marginTop: 2,
                  }}
                >
                  {s.value === s.target ? "✓ VERIFIED" : "✗ INTEGRITY VIOLATION"}
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
            <span style={{ color: "#e0e0e0" }}>{stats.theorems}</span>
          </span>
          <span>
            definitions:{" "}
            <span style={{ color: "#e0e0e0" }}>{stats.definitions}</span>
          </span>
          <span>
            axioms:{" "}
            <span style={{ color: "#e0e0e0" }}>{stats.axioms}</span>
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
          gap: 2,
          padding: "10px 28px",
          borderBottom: "1px solid #1a1a1a",
          flexWrap: "wrap",
        }}
      >
        {Object.entries(PAPER_NAMES).map(([key, name]) => (
          <button
            key={key}
            onClick={() =>
              setHighlightPaper(
                highlightPaper === Number(key) ? null : Number(key)
              )
            }
            style={{
              background:
                highlightPaper === Number(key)
                  ? PAPER_COLORS[Number(key)] + "20"
                  : "transparent",
              border: `1px solid ${
                highlightPaper === Number(key)
                  ? PAPER_COLORS[Number(key)]
                  : "#222"
              }`,
              borderRadius: 4,
              padding: "4px 10px",
              cursor: "pointer",
              display: "flex",
              alignItems: "center",
              gap: 6,
              fontSize: 10,
              color:
                highlightPaper === Number(key)
                  ? PAPER_COLORS[Number(key)]
                  : "#888",
              transition: "all 0.15s",
            }}
          >
            <span
              style={{
                width: 8,
                height: 8,
                borderRadius: "50%",
                background: PAPER_COLORS[Number(key)],
                display: "inline-block",
              }}
            />
            {name}
          </button>
        ))}
      </div>

      {/* Graph */}
      <div style={{ padding: "0 28px" }}>
        <ForceGraph
          data={activeData}
          width={900}
          height={500}
          highlightPaper={highlightPaper}
        />
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
        To reject any node in this graph, trace the dependency chain to its root.
        The root is ℕ. To reject any definition, you must reject counting.
      </div>
    </div>
  );
}
