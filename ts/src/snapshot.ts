/**
 * Render snapshots — convert the verified port's real structures into plain
 * node/edge data the visualization can draw.  This is the seam that lets
 * `kb/memory-graph.html` be driven by the *verified* operations instead of
 * hand-rolled logic.
 */
import { type Chain, type Packet } from "./deque.js";
import { bufColor, colorMeet, type Color } from "./buf5.js";
import {
  type Cchain,
  type Cnode,
  type Cpacket,
  rootAndChild,
  nodeColor,
  chainHasNode,
} from "./cadeque.js";

// ---------- §4 deque ----------
export interface Cell4 {
  id: string;
  depth: number; // pair-tower level (0 = base elements, k = 2^k bundles)
  pre: number;
  suf: number;
  color: Color;
  anchor: boolean; // outer level of a ChainCons packet (green/red boundary)
  ending: boolean;
}
export interface Snap4 {
  cells: Cell4[];
}

/** Flatten a Chain top→bottom into one cell per level; mark the ChainCons
 *  packet boundaries as anchors (an anchor begins a new packet — the cells of
 *  one packet share a single allocation, drawn enclosed in memory-graph.html). */
export function snapshot4<A>(c: Chain<A>): Snap4 {
  const cells: Cell4[] = [];
  let depth = 0;
  let cur: Chain<A> = c;
  for (;;) {
    if (cur.tag === "end") {
      cells.push({ id: `L${depth}`, depth, pre: cur.b.length, suf: 0, color: bufColor(cur.b), anchor: true, ending: true });
      return { cells };
    }
    let p: Packet<A> = cur.p;
    let first = true;
    while (p.tag === "pnode") {
      cells.push({
        id: `L${depth}`,
        depth,
        pre: p.pre.length,
        suf: p.suf.length,
        color: colorMeet(bufColor(p.pre), bufColor(p.suf)),
        anchor: first,
        ending: false,
      });
      depth++;
      first = false;
      p = p.inner;
    }
    cur = cur.c; // continue with the chain below this packet (plugs into the Hole)
  }
}

// ---------- §6 catenable deque ----------
export type Color4 = "green" | "yellow" | "orange" | "red";
export interface Node6 {
  id: string;
  role: string; // only | left | right | pair
  pre: number;
  suf: number;
  color: Color4;
  depth: number;
}
export interface Edge6 {
  from: string;
  to: string;
  kind: "left" | "right" | "child";
}
export interface Snap6 {
  nodes: Node6[];
  edges: Edge6[];
}

const gyorToColor = (g: ReturnType<typeof nodeColor>): Color4 =>
  g === "CG" ? "green" : g === "CY" ? "yellow" : g === "CO" ? "orange" : "red";

/** Walk the Cchain tree into nodes (triples) + parent→child edges, using the
 *  same root_and_child decomposition the algorithm uses; a node's child that is
 *  a CPair becomes two (left,right) edges — the §6 two6 branching. */
export function snapshot6<A>(root: Cchain<A>): Snap6 {
  const nodes: Node6[] = [];
  const edges: Edge6[] = [];
  let counter = 0;
  const fresh = () => `T${counter++}`;

  const walk = (c: Cchain<A>, parent: string | null, kind: Edge6["kind"], depth: number): void => {
    if (c.tag === "cempty") return;
    if (c.tag === "cpair") {
      if (parent === null) {
        const id = fresh();
        nodes.push({ id, role: "pair", pre: 0, suf: 0, color: "green", depth });
        walk(c.l, id, "left", depth + 1);
        walk(c.r, id, "right", depth + 1);
      } else {
        walk(c.l, parent, "left", depth);
        walk(c.r, parent, "right", depth);
      }
      return;
    }
    // csingle
    const p: Cpacket<A> = c.p;
    const [n, child]: [Cnode<A>, Cchain<A>] = rootAndChild(p, c.rest);
    const id = fresh();
    nodes.push({
      id,
      role: n.k,
      pre: n.pre.length,
      suf: n.suf.length,
      color: gyorToColor(nodeColor(chainHasNode(child), n)),
      depth,
    });
    if (parent !== null) edges.push({ from: parent, to: id, kind });
    walk(child, id, "child", depth + 1);
  };

  walk(root, null, "child", 0);
  return { nodes, edges };
}
