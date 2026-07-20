# reticulate benchmarks — v1.0.0

86 §2.1-conformant binary session-type protocols (the corpus the ICE 2026 lattice result is validated on). Each entry: `name`, `type` (session-type string), `description`, expected `states`/`transitions`/`sccs`, `uses_parallel`.

Every protocol parses under the six-constructor §2.1 grammar and its state space is a bounded lattice. Parallel-with-continuation and multiparty protocols are out of v1.0.0.
