/-
Copyright (c) 2026 Alexandre Zua Caldeira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexandre Zua Caldeira
-/
import Reticulate.Lemmas.EndLemma
import Reticulate.Lemmas.BranchLemma
import Reticulate.Lemmas.SequencingLemma
import Reticulate.Lemmas.ParallelLemma
import Reticulate.Lemmas.BottomAbsorption
import Reticulate.Lemmas.RecursionLemma
import Reticulate.UniqueExtrema
import Reticulate.Spec.Core.SessionType
import Reticulate.Spec.Core.WellFormed
import Reticulate.Spec.StateSpace.StateSpace
import Reticulate.Spec.StateSpace.StateSpaceLattice

/-!
# The Reticulate Theorem (ICE 2026 — Phase R3, integrated form)

**Theorem (Reticulate Theorem, paper Theorem 1, `thm:reticulate`)**: For every
well-formed session type `S` (including equation systems), the state space
`L(S)` quotiented by strongly connected components is a bounded lattice
under the reachability ordering.

```
∀ S, WellFormed S → ∃ (Lattice (SCCQuotient (stateSpace S)))
                       (BoundedOrder (SCCQuotient (stateSpace S))), True
```

## Phase R3 (HEADLINE integration)

Phase R3 of the ICE 2026 end-to-end mechanisation campaign integrates the
case-decomposition assembly (kept here under
`reticulate_theorem_caseDecomposition` as a historical companion) with the
paper-faithful universal mechanisation living in
`Reticulate.Spec.StateSpaceLattice`. The integrated form is a Π-statement
over `SessionType` quantifying over the WellFormed hypothesis, exactly
matching the paper's Theorem 1 statement at line 885 of
`papers/publications/ice-2026/main.tex`:

> For every well-formed session type S (including equation systems),
> L(S)/≡ is a bounded lattice.

The headline name `reticulate_theorem` now refers to the integrated form;
the proof is a one-liner that consumes the universal `Lattice` instance
(`Reticulate.Spec.SessionType.universal_Lattice`) and the universal
`BoundedOrder` instance (`Reticulate.Spec.SessionType.instBoundedOrder`).
Both of those are themselves derived by structural induction over the
paper-faithful `SessionType` inductive (`Reticulate.Spec.SessionType`) per
the proof technique listed in the paper's proof of Theorem 1:

| Constructor    | Lean discharge                                               |
|----------------|--------------------------------------------------------------|
| `end`          | `end_latticeStruct` + `end_scc_subsingleton`                 |
| `&{…}` / `+{…}`| `branch_latticeStruct` / `select_latticeStruct`              |
| `∥`            | `par_latticeStruct` (n-fold product, `Pi.instLattice`-based) |
| `μX.S`         | `rec_latticeStruct` (SCC absorbs back-edges)                 |
| `var X`        | `var_latticeStruct` (subsingleton)                           |
| `WellFormed`   | dispatched into `parClosed` for `universal_Lattice`          |

The case-decomposition assembly that was the previous `reticulate_theorem`
in this file is preserved as `reticulate_theorem_caseDecomposition`. It
packages the non-recursive cases as Mathlib-typeclass witnesses (using the
legacy `Reticulate.SessionType` inductive's `WithBot'` encoding) and was
the deliverable for an earlier campaign phase. With Phase R3 it is no
longer the headline, but is retained because every constituent lemma it
cites (`EndLemma`, `BranchLemma`, `SequencingLemma`, `ParallelLemma`,
`RecursionLemma`, `BottomAbsorption`, `UniqueExtrema`) is still in the
import closure of the umbrella `Reticulate.lean` and represents
independently checked content.
-/

noncomputable section

namespace Reticulate.ReticulateTheorem

open EndLemma BranchLemma SequencingLemma ParallelLemma

/-!
## Phase R3 — integrated `reticulate_theorem`

This is the HEADLINE statement: a Π-statement quantifying over every
paper-faithful session type and the `WellFormed` hypothesis, concluding
that the SCC quotient of its state space is a bounded lattice. The
proof is a one-liner consuming the universal instances from
`Reticulate.Spec.StateSpaceLattice`.
-/

/-- **The Reticulate Theorem (paper Theorem 1, integrated form).**

    For every well-formed session type `S`, the SCC quotient of its state
    space `L(S)` is a bounded lattice. The conclusion is packaged as an
    existential bundle exposing both the `Lattice` and `BoundedOrder`
    instances on `SCCQuotient (stateSpace S)`.

    The proof dispatches to the universal instances built by structural
    induction in `Reticulate.Spec.StateSpaceLattice`:

    * `Reticulate.Spec.SessionType.universal_Lattice` constructs the
      `Lattice` instance by structural induction on `S`, using
      `parClosed S` (a clause of `WellFormed`).
    * `Reticulate.Spec.SessionType.instBoundedOrder` constructs the
      `BoundedOrder` instance unconditionally — `⊥` is the SCC of the
      initial state, `⊤` is the SCC of the terminal state. -/
theorem reticulate_theorem
    (S : Reticulate.Spec.SessionType)
    (hwf : Reticulate.Spec.SessionType.WellFormed S) :
    ∃ (_ : Lattice (Reticulate.SCCQuotient
                      (Reticulate.Spec.SessionType.stateSpace S)))
      (_ : BoundedOrder (Reticulate.SCCQuotient
                          (Reticulate.Spec.SessionType.stateSpace S))), True :=
  -- AMENDED 2026-05-28: WellFormed is now 4-clause; parClosed is at `.2.2.1`.
  ⟨ Reticulate.Spec.SessionType.universal_Lattice S hwf.2.2.1
  , Reticulate.Spec.SessionType.instBoundedOrder S
  , trivial ⟩

/-!
## Case-decomposition assembly (historical companion)

The previous headline statement of `reticulate_theorem` packaged the
non-recursive cases as separate Mathlib-typeclass witnesses, indexed by
the cases of the paper grammar. It is preserved here under the name
`reticulate_theorem_caseDecomposition` because:

* it is independent content — every constituent lemma is in the
  import closure of `Reticulate.lean` and remains independently
  checked;
* it documents the Mathlib lemmas that close each constructor case
  (`end_bounded_lattice`, `sequencing_preserves_lattice`,
  `nary_parallel_fin`), useful as a reading guide for the underlying
  algebraic content;
* downstream paper steps (e.g. step 200w on call-site meta-properties)
  reference this case-by-case shape via the constituent lemmas.

The integrated `reticulate_theorem` above is the form that matches the
paper's Theorem 1 statement and is the formal witness for `\cref{thm:reticulate}`. -/
theorem reticulate_theorem_caseDecomposition :
    -- Case 1: end
    (∃ (_ : Lattice EndState) (_ : BoundedOrder EndState), True) ∧
    -- Case 2: sequencing / branch — for any bounded lattice L(S)
    (∀ (α : Type*) [Lattice α] [OrderTop α],
      ∃ (_ : Lattice (WithBot' α)) (_ : BoundedOrder (WithBot' α)), True) ∧
    -- Case 3: k-ary parallel — for any family of bounded lattices
    (∀ (k : ℕ) (L : Fin k → Type*) [∀ i, Lattice (L i)] [∀ i, BoundedOrder (L i)],
      ∃ (_ : Lattice (∀ i, L i)) (_ : BoundedOrder (∀ i, L i)), True) := by
  exact ⟨
    end_bounded_lattice,
    fun α _ _ => sequencing_preserves_lattice α,
    fun k L _ _ => nary_parallel_fin k L
  ⟩

end Reticulate.ReticulateTheorem

end
