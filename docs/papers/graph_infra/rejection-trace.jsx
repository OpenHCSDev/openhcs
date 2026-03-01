import { useState, useEffect, useRef, useMemo } from "react";
import * as d3 from "d3";

// ── Theme (only visual constants, zero domain knowledge) ──
const TH = {
  bg: "#0a0a0a", fg: "#e0e0e0", dim: "#555", border: "#1a1a1a",
  ok: "#10b981", bad: "#ef4444", warn: "#f59e0b", info: "#3b82f6",
  font: "'JetBrains Mono','SF Mono',monospace",
  palette: ["#ef4444","#3b82f6","#8b5cf6","#10b981","#ec4899","#f59e0b","#06b6d4","#f97316"],
};

// ── Pure graph algorithms ──
const eIds = e => [typeof e.source==="object"?e.source.id:e.source, typeof e.target==="object"?e.target.id:e.target];
function buildAdj(nodes, edges) { const a={}; for(const n of nodes)a[n.id]=[]; for(const e of edges){const[s,t]=eIds(e);if(a[s])a[s].push(t);} return a; }
function findRoots(nodes, adj) { return new Set(nodes.filter(n=>(adj[n.id]||[]).length===0).map(n=>n.id)); }
function bfs(start, adj, targets) {
  if(targets.has(start))return[start];
  const v=new Set([start]),par={},q=[start];
  while(q.length){const c=q.shift();if(targets.has(c)){const p=[];for(let n=c;n!==undefined;n=par[n])p.unshift(n);return p;}
  for(const nb of adj[c]||[])if(!v.has(nb)){v.add(nb);par[nb]=c;q.push(nb);}} return[start];
}
function countComponents(nodes, edges) {
  const u={}; for(const n of nodes)u[n.id]=[]; for(const e of edges){const[s,t]=eIds(e);u[s]?.push(t);u[t]?.push(s);}
  const v=new Set(); let c=0;
  for(const n of nodes){if(v.has(n.id))continue;c++;const q=[n.id];while(q.length){const x=q.shift();if(v.has(x))continue;v.add(x);q.push(...(u[x]||[]).filter(y=>!v.has(y)));}} return c;
}
function analyze(data) {
  const adj=buildAdj(data.nodes,data.edges), roots=findRoots(data.nodes,adj);
  let maxD=0; for(const n of data.nodes){maxD=Math.max(maxD,bfs(n.id,adj,roots).length-1);}
  return { total:data.nodes.length, edges:data.edges.length, components:countComponents(data.nodes,data.edges),
    maxDepth:maxD, groups:[...new Set(data.nodes.map(n=>n.group).filter(Boolean))] };
}

// ── Stat cell ──
const Stat = ({value,label,color,check}) => (
  <div style={{padding:"10px 16px",borderRight:`1px solid ${TH.border}`,minWidth:70}}>
    <div style={{fontFamily:TH.font,fontSize:22,fontWeight:800,color,lineHeight:1}}>{value}</div>
    <div style={{fontFamily:TH.font,fontSize:8,color:TH.dim,letterSpacing:"0.1em",marginTop:4}}>
      {label}{check&&<span style={{color:TH.ok,marginLeft:4}}>✓</span>}
    </div>
  </div>
);

// ── Chain panel ──
function Chain({path,nodeMap,gc,onClose}) {
  const defs=path.filter(id=>nodeMap[id]?.kind==="definition").length, isRoot=path.length<=1;
  return (
    <div style={{fontFamily:TH.font,position:"fixed",right:0,top:0,bottom:0,width:340,background:"#0d0d0d",borderLeft:`1px solid ${TH.border}`,zIndex:100,display:"flex",flexDirection:"column",overflow:"hidden"}}>
      <div style={{padding:"14px 18px",borderBottom:`1px solid ${TH.border}`,display:"flex",justifyContent:"space-between",alignItems:"center"}}>
        <div>
          <div style={{fontSize:11,letterSpacing:"0.1em",color:TH.dim}}>REJECTION CHAIN</div>
          <div style={{fontSize:10,color:TH.dim,marginTop:2}}>
            {isRoot?<span style={{color:TH.bad}}>ROOT AXIOM</span>:<><span style={{color:TH.warn}}>{path.length-1}</span> hops · <span style={{color:TH.warn}}>{defs}</span> defs</>}
          </div>
        </div>
        <button onClick={onClose} style={{fontFamily:TH.font,background:"none",border:`1px solid ${TH.border}`,borderRadius:4,color:TH.dim,cursor:"pointer",padding:"3px 8px",fontSize:11}}>✕</button>
      </div>
      <div style={{flex:1,overflowY:"auto",padding:"14px 18px"}}>
        {path.map((id,i)=>{const n=nodeMap[id],last=i===path.length-1,col=gc(n?.group);return(
          <div key={id} style={{display:"flex",gap:10}}>
            <div style={{display:"flex",flexDirection:"column",alignItems:"center",minWidth:16}}>
              <div style={{width:last?12:8,height:last?12:8,borderRadius:n?.kind==="definition"?2:"50%",background:last?TH.bad:col,flexShrink:0}}/>
              {!last&&<div style={{width:1,height:28,background:TH.border}}/>}
            </div>
            <div style={{paddingBottom:last?0:8}}>
              <div style={{fontSize:11,fontWeight:600,color:last?TH.bad:TH.fg,wordBreak:"break-all"}}>
                {id} <span style={{fontSize:7,color:col}}>{(n?.kind||"").toUpperCase()}</span>
              </div>
              <div style={{fontSize:9,color:TH.dim}}>
                {n?.group||""}
                {i===0&&!isRoot&&<span style={{color:TH.warn,marginLeft:6}}>← reject this</span>}
                {last&&!isRoot&&<span style={{color:TH.bad,marginLeft:6}}>← must reject this</span>}
              </div>
            </div>
          </div>);})}
      </div>
    </div>
  );
}

// ── Force graph ──
function Graph({data,w,h,selected,setSelected,pathSet,pathEdges,gc}) {
  const ref=useRef(null), r=useRef({});
  useEffect(()=>{
    if(!ref.current)return; const el=d3.select(ref.current);el.selectAll("*").remove();
    const g=el.append("g"); el.call(d3.zoom().scaleExtent([0.1,10]).on("zoom",e=>g.attr("transform",e.transform)));
    const ns=data.nodes.map(d=>({...d})),es=data.edges.map(d=>({...d}));
    const sim=d3.forceSimulation(ns).force("link",d3.forceLink(es).id(d=>d.id).distance(35).strength(0.4))
      .force("charge",d3.forceManyBody().strength(-50).distanceMax(200)).force("center",d3.forceCenter(w/2,h/2)).force("collide",d3.forceCollide(8));
    const link=g.append("g").selectAll("line").data(es).join("line").attr("stroke","#ffffff0a").attr("stroke-width",0.5);
    const node=g.append("g").selectAll("circle").data(ns).join("circle")
      .attr("r",d=>d.kind==="axiom"?7:d.kind==="definition"?5:4).attr("fill",d=>gc(d.group)).attr("opacity",0.9).style("cursor","pointer")
      .on("click",(ev,d)=>{ev.stopPropagation();setSelected(d.id);})
      .call(d3.drag().on("start",(e,d)=>{if(!e.active)sim.alphaTarget(0.3).restart();d.fx=d.x;d.fy=d.y;})
        .on("drag",(e,d)=>{d.fx=e.x;d.fy=e.y;}).on("end",(e,d)=>{if(!e.active)sim.alphaTarget(0);d.fx=d.fy=null;}));
    node.append("title").text(d=>`${d.id} (${d.kind||"?"}) [${d.group||"?"}]`);
    sim.on("tick",()=>{link.attr("x1",d=>d.source.x).attr("y1",d=>d.source.y).attr("x2",d=>d.target.x).attr("y2",d=>d.target.y);node.attr("cx",d=>d.x).attr("cy",d=>d.y);});
    r.current={node,link}; el.on("click",()=>setSelected(null)); return()=>sim.stop();
  },[data,w,h]);
  useEffect(()=>{const{node,link}=r.current;if(!node)return;
    node.transition().duration(150).attr("opacity",d=>!selected?0.9:pathSet.has(d.id)?1:0.05)
      .attr("r",d=>{const b=d.kind==="axiom"?7:d.kind==="definition"?5:4;return selected&&pathSet.has(d.id)?b+2:b;});
    link.transition().duration(150).attr("stroke",d=>{if(!selected)return"#ffffff0a";return pathEdges.has(`${eIds(d)[0]}->${eIds(d)[1]}`)?TH.warn+"80":"#ffffff03";})
      .attr("stroke-width",d=>!selected?0.5:pathEdges.has(`${eIds(d)[0]}->${eIds(d)[1]}`)?2:0.3);
  },[selected,pathSet,pathEdges]);
  return <svg ref={ref} width={w} height={h} style={{background:TH.bg,borderRadius:4}}/>;
}

// ── Main ──
export default function RejectionTrace() {
  const [data,setData]=useState(null),[selected,setSelected]=useState(null),[buf,setBuf]=useState("");
  const load=raw=>{try{const d=JSON.parse(raw);if(d.nodes&&d.edges)setData(d);}catch{}};
  const stats=useMemo(()=>data?analyze(data):null,[data]);
  const nodeMap=useMemo(()=>{const m={};(data?.nodes||[]).forEach(n=>m[n.id]=n);return m;},[data]);
  const gcMap=useMemo(()=>{const m={};(stats?.groups||[]).forEach((g,i)=>m[g]=TH.palette[i%TH.palette.length]);return m;},[stats]);
  const gc=g=>gcMap[g]||TH.dim;
  const roots=useMemo(()=>data?findRoots(data.nodes,buildAdj(data.nodes,data.edges)):new Set(),[data]);
  const path=useMemo(()=>selected&&data?bfs(selected,buildAdj(data.nodes,data.edges),roots):[], [selected,data,roots]);
  const pathSet=useMemo(()=>new Set(path),[path]);
  const pathEdges=useMemo(()=>{const s=new Set();for(let i=0;i<path.length-1;i++)s.add(`${path[i]}->${path[i+1]}`);return s;},[path]);

  if(!data) return (
    <div style={{fontFamily:TH.font,background:TH.bg,color:TH.fg,height:"100vh",display:"flex",flexDirection:"column",alignItems:"center",justifyContent:"center",gap:16}}>
      <div style={{fontSize:14,fontWeight:700,letterSpacing:"0.08em"}}>REJECTION TRACE</div>
      <div style={{fontSize:10,color:TH.dim}}>Paste JSON from Lean <code>#export_graph_json</code></div>
      <textarea value={buf} onChange={e=>setBuf(e.target.value)} placeholder='{"nodes":[{"id":"...","kind":"theorem","group":"..."}],"edges":[{"source":"...","target":"..."}]}'
        style={{fontFamily:TH.font,width:500,height:120,background:"#111",border:`1px solid ${TH.border}`,borderRadius:4,color:TH.dim,fontSize:10,padding:10,resize:"vertical"}}/>
      <button onClick={()=>load(buf)} style={{fontFamily:TH.font,background:"#1a1a1a",border:`1px solid ${TH.border}`,borderRadius:4,color:TH.fg,fontSize:10,padding:"8px 20px",cursor:"pointer"}}>LOAD</button>
    </div>);

  return (
    <div style={{fontFamily:TH.font,background:TH.bg,color:TH.fg,height:"100vh",display:"flex",flexDirection:"column",overflow:"hidden"}}>
      <div style={{padding:"12px 18px",borderBottom:`1px solid ${TH.border}`,display:"flex",alignItems:"baseline",gap:10}}>
        <span style={{fontSize:13,fontWeight:700,letterSpacing:"0.08em"}}>REJECTION TRACE</span>
        <span style={{fontSize:9,color:TH.dim}}>CLICK NODE · TRACE TO ROOT</span>
      </div>
      <div style={{display:"flex",borderBottom:`1px solid ${TH.border}`}}>
        <Stat value={0} label="SORRY" color={TH.ok} check/>
        <Stat value={stats.components} label="COMPONENTS" color={stats.components===1?TH.ok:TH.bad} check={stats.components===1}/>
        <Stat value={stats.maxDepth} label="MAX DEPTH" color={TH.warn}/>
        <Stat value={stats.total} label="NODES" color={TH.info}/>
      </div>
      <div style={{display:"flex",gap:4,padding:"6px 18px",borderBottom:`1px solid ${TH.border}`,flexWrap:"wrap"}}>
        {stats.groups.map(g=><span key={g} style={{fontSize:9,color:TH.dim,display:"flex",alignItems:"center",gap:4,padding:"2px 6px"}}>
          <span style={{width:7,height:7,borderRadius:"50%",background:gc(g)}}/>{g}</span>)}
      </div>
      <div style={{flex:1,position:"relative",overflow:"hidden"}}>
        <Graph data={data} w={selected?650:1000} h={500} selected={selected} setSelected={setSelected} pathSet={pathSet} pathEdges={pathEdges} gc={gc}/>
        {selected&&<Chain path={path} nodeMap={nodeMap} gc={gc} onClose={()=>setSelected(null)}/>}
      </div>
    </div>);
}
