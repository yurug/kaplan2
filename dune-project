(lang dune 3.22)
(using rocq 0.12)
(name ktdeque)
(license MIT)
(authors "Yann Régis-Gianas and contributors")
(maintainers "yann.regis-gianas@nomadic-labs.com")
(source (uri "git+https://github.com/yurug/kaplan2"))
(homepage "https://github.com/yurug/kaplan2")
(bug_reports "https://github.com/yurug/kaplan2/issues")
(generate_opam_files true)

; Disable the deprecation warning for the legacy coq language; we use rocq.
(warnings (deprecated_coq_lang disabled))

; Public package: the verified Coq-extracted KT-deque.
(package
 (name ktdeque)
 (synopsis "Kaplan-Tarjan persistent real-time deque (Coq-extracted, worst-case O(1))")
 (description
   "A purely-functional, persistent, double-ended queue with worst-case O(1) per operation: push, pop, inject, eject all run in constant time.  The OCaml code in this package is automatically extracted from the Rocq formalization in the kaplan2 repository.  The extraction is proven sequence-preserving in the source theorems, so this OCaml is the verified front-end for the algorithm.  For the C port (1.6x-2.9x faster than this OCaml on every workload at n=1M with arena compaction), see the c/ directory of the source repo.")
 (depends
  (ocaml (>= 4.14))
  dune)
 (tags ("data-structures" "deque" "persistent" "verified" "kaplan-tarjan")))
