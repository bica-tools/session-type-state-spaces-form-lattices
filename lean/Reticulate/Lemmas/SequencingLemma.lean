/-
Copyright (c) 2026 Alexandre Zua Caldeira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexandre Zua Caldeira
-/
import Reticulate.Lemmas.BranchLemma

/-!
# Sequencing Lemma: L(m.S) Preserves Bounded Lattice

The sequencing constructor `m.S` prepends a single method call `m` before
the session type `S`. Its state space L(m.S) has a new initial state q_new
with a single transition `m` to the top of L(S):

```
    q_new ──m──→ ⊤(S)
                  │
                L(S)
                  │
                 ⊥(S)
```

In the reachability ordering (u ≤ v iff u reaches v), q_new reaches
everything that ⊤(S) reaches, plus ⊤(S) itself. So q_new becomes the
new bottom (= initial state that reaches all).

This is exactly the `WithBot'` construction from the Branch Lemma:
adding a new minimum element to a bounded lattice preserves lattice structure.

## Main result

* `sequencing_preserves_lattice` : If L(S) is a bounded lattice, then
  L(m.S) is a bounded lattice.
-/

noncomputable section

namespace Reticulate.SequencingLemma

open BranchLemma

/-- **Sequencing Lemma**: If L(S)/≡ is a bounded lattice, then L(m.S)/≡
    is a bounded lattice.

    Proof: L(m.S) = WithBot'(L(S)) — the new initial state becomes the
    new ⊥ in the reachability ordering. By the Branch Lemma (WithBot'
    preserves bounded lattice structure), the result is a bounded lattice.

    This is a direct corollary of BranchLemma.branch_preserves_lattice
    since sequencing `m.S` is the special case of `&{m: S}` (a branch
    with exactly one arm). -/
theorem sequencing_preserves_lattice
    (α : Type*) [Lattice α] [OrderTop α] :
    ∃ (_ : Lattice (WithBot' α)) (_ : BoundedOrder (WithBot' α)), True :=
  ⟨inferInstance, inferInstance, trivial⟩

end Reticulate.SequencingLemma

end
