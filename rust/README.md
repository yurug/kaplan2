# Rust — port (work in progress)

A Rust port of the algorithm. Currently a placeholder — the heavy
lifting is happening in [`../c/`](../c/) for now.

## Layout

```
rust/
├── Cargo.toml
├── Cargo.lock
└── ktdeque-deque4/   -- the crate (the older D4Cell variant)
```

## Build

```sh
cd rust
cargo build --release
cargo test
```

## Status

- Older D4Cell variant only. The newer DequePtr port (matching the
  current Rocq formalization) hasn't been ported yet.
- Not benchmarked against Viennot.

Contributions welcome.
