# Session Type State Spaces Form Lattices — companion artifact

Reproduction artifact for the ICE 2026 paper *Session Type State Spaces Form
Lattices* (A. Zua Caldeira). The paper is published separately (ICE 2026 / EPTCS);
this self-contained record is its code-and-data companion, scoped to the paper's
results.

```
lean/        Lean 4 mechanisation of the Reticulate Theorem (import closure of reticulate_lattice)
tool/        the Python `reticulate` lattice checker (parser -> state space -> lattice check)
benchmarks/  the 86 §2.1-conformant protocol benchmarks
```

## What each paper claim maps to

| Paper claim | Where | How to reproduce |
|---|---|---|
| **Thm 15** (Reticulate Theorem): every well-formed session type's SCC-quotient state space is a bounded lattice | `lean/Reticulate/Spec/StateSpace/StateSpaceLattice/Universal.lean` (`reticulate_lattice`) | `cd lean && lake exe cache get && lake build` — a successful build IS the proof (zero `sorry`) |
| **All benchmarks form lattices** | `tool/` + `benchmarks/` | `python -m reticulatep.cli "<type>"` per protocol, or the benchmark test suite in `tool/tests/` |
| **86% / 14% distributive split** | `tool/` (`--distributive`) | run the distributivity check across `benchmarks/` |
| **Fig 2 / worked examples** (e.g. SMTP: 3 states) | `tool/` | `python -m reticulatep.cli "rec X . &{mail: &{send: X}, quit: end}"` |
| **Cross-tool agreement** (Python + Java) | `tool/` (Python side) | the Java checker (BICA Reborn) is the independent second implementation; see Scope below |

## Scope (read this)

This artifact backs the paper's **headline result** — the Reticulate Theorem —
end to end: the Lean development mechanises it (zero `sorry`, no coinduction),
and the Python tool reproduces the state-space construction and lattice checks
on the benchmark corpus. Python and Lean agree by a compiled cross-tool parity
check on the conformant corpus (`CanonicalStateSpace` = `reticulateP`
cell-by-cell).

Deliberately **not** in this artifact:
- The paper's *auxiliary* mechanised results (duality, width-subtyping
  embedding, the realisable fragment, the divergent-recursion counterexample)
  live in the same Lean development and are available on request / in a later
  release; this artifact ships the theorem's import closure.
- The 22 parallel-with-continuation benchmarks (the paper's 108 = 86 conformant
  + 22 held-out expressivity corpus) are not §2.1-conformant and are excluded
  here by design.
- The Java checker source (the independent second implementation) is
  distributed separately.

## Provenance

A frozen snapshot of the `reticulate` toolchain — the Python lattice checker,
the Lean 4 mechanisation, and the protocol benchmark corpus — as of the ICE 2026
camera-ready.

## License

MIT (see `LICENSE`); the same license applies to the whole artifact.
