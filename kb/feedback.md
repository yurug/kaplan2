- The directory ocaml/ is not ready for distribution:
  - it must be self-contained: except the extracted code from Rocq, it should not depend on other part of the repository. Even the extracted code must be put there by an external mean.
  - no opam package
  - no clean official library: there are many OCaml implementations to ease benchmarks but the library we want to distribute is not clear.
  - the README.md should be self-contained, pedagogical, etc.
  - the test suite should be clear
  
- The directory c/ is a complete mess and does not match the standard of C packages distribution.
  - It must also be self-contained.
  
  
- Some markdown files are not consistent with the codebase and reciprocally.

