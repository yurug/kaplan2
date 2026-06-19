/**
 * Public API of the §4 Kaplan–Tarjan deque (TypeScript port).
 *
 *   import * as KT from "./index.js";
 *   let d = KT.empty<number>();
 *   d = KT.push(1, d);            // front
 *   d = KT.inject(d, 2);          // back
 *   const r = KT.pop(d);          // r = [value, deque] | null
 *
 * Persistent: every op returns a new deque; old handles stay valid.
 */
export type { Chain as Deque } from "./deque.js";
export {
  emptyChain as empty,
  push,
  inject,
  pop,
  eject,
  toList,
  length,
  checkRegular,
} from "./deque.js";
export type { Elt } from "./element.js";
export type { Color } from "./buf5.js";
