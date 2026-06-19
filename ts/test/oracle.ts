/**
 * Naive reference deque — the "obviously correct" ground truth the port is
 * differentially tested against (the JS analogue of the doubly-linked-list
 * `ref_deque` in `c/tests/test.c` / `c/tests/fuzz.c`).  Backed by a plain
 * array; O(n) per op, but trivially correct.
 */
export class Oracle<A> {
  private xs: A[] = [];

  push(x: A): void {
    this.xs.unshift(x);
  } // front
  inject(x: A): void {
    this.xs.push(x);
  } // back
  pop(): A | undefined {
    return this.xs.shift();
  }
  eject(): A | undefined {
    return this.xs.pop();
  }
  get length(): number {
    return this.xs.length;
  }
  toList(): A[] {
    return this.xs.slice();
  }
}
