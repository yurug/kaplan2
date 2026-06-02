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
 (synopsis "Kaplan-Tarjan persistent real-time deque (Rocq-extracted)")
 (description
   "A purely-functional, persistent, double-ended queue extracted from the Rocq formalization in the kaplan2 repository.  The current public theorem bundle packages sequence correctness and regularity preservation for the extracted push, pop, inject, and eject family; the repository release gate tracks the remaining totality and chain-level cost theorems before making an unqualified mechanically verified worst-case O(1) claim.  Catenable experiments remain in a private workspace library and are not part of the installable public package.  Performance is competitive with Viennot et al.'s hand-written real-time deque (within ~15% on standard workloads at n=1M).")
 (depends
  (ocaml (>= 4.14))
  dune
  (qcheck :with-test)
  (qcheck-core :with-test))
 (tags ("data-structures" "deque" "persistent" "rocq" "kaplan-tarjan")))
