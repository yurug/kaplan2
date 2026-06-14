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

; Public package: the Rocq-extracted KT-deque.
(package
 (name ktdeque)
 (synopsis "Kaplan-Tarjan persistent real-time deque, with O(1) catenation")
 (description
   "A purely-functional, persistent double-ended queue with worst-case O(1) push, pop, inject and eject, plus worst-case O(1) catenation.  The implementation is extracted from a Rocq (Coq 9.1) formalization whose keystone theorems are closed with zero admits: totality, sequence preservation, the regularity invariant, and a constant per-operation cost bound, for both the section-4 deque (deque_wc_o1_*) and the section-6 catenable deque (cat_keystone_* + cat_wc_o1).  The package exposes an idiomatic interface -- open Ktdeque and use the Deque module (push/inject/pop/eject) or Cadeque (the same, plus concat) -- over the extracted code (the raw extraction is available as the internal sub-library ktdeque.extracted).  On the benchmark suite the extracted artifact is faster than Viennot et al.'s hand-written OCaml cadeque on every workload at n=1M.")
 (depends
  (ocaml (>= 4.14))
  dune
  (qcheck :with-test)
  (qcheck-core :with-test))
 (tags ("data-structures" "deque" "persistent" "rocq" "kaplan-tarjan")))
