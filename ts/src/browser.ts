/**
 * Browser entry point — bundled (esbuild --format=iife --global-name=KTDeque)
 * into `kb/ktdeque.bundle.js`, which the visualization loads with a classic
 * <script src> (works from file://).  Exposes the verified §4 and §6 operations
 * plus their render snapshots, so `kb/memory-graph.html` is driven by the
 * differentially-tested port instead of hand-rolled logic.
 */
import * as D from "./deque.js";
import * as C from "./cadeque.js";
export { snapshot4, snapshot6 } from "./snapshot.js";

// §4 deque
export const empty4 = D.emptyChain;
export const push4 = D.push;
export const inject4 = D.inject;
export const pop4 = D.pop;
export const eject4 = D.eject;
export const toList4 = D.toList;

// §6 catenable deque
export const empty6 = C.cadEmpty;
export const push6 = C.cadPush;
export const inject6 = C.cadInject;
export const pop6 = C.cadPop;
export const eject6 = C.cadEject;
export const concat6 = C.cadConcatChecked;
export const toList6 = C.cadToList;

export type { Chain as Deque4 } from "./deque.js";
export type { Cchain as Deque6 } from "./cadeque.js";
