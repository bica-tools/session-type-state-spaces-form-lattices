/-
Copyright (c) 2026 Alexandre Zua Caldeira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexandre Zua Caldeira
-/

import Reticulate.Spec.StateSpace.StateSpace

/-!
# Edge-list characterisations for the `par` builder

The state-space builder for parallel composition (`par ss`) is
nested through four helper functions whose bodies do arithmetic on
the row-major product encoding. To reason about the resulting
edges later — in particular to prove that the par-component
reachability lifts and unlifts correctly — we first need
membership rewrites: "an edge `(src, tgt)` belongs to this helper's
output iff there exist indices `p, q` such that …".

This module provides exactly those rewrites and nothing more. No
reachability reasoning, no lattice theory; pure arithmetic.

What is exported.
* `mem_edgeListParLiftSuffix` — innermost layer: iterates the
  suffix-coordinate `q` over `[q0, suffixProd)` and emits
  one componentwise edge per `q`.
* `mem_edgeListParLiftOne` — middle layer: iterates the
  prefix-coordinate `p` over `[p0, prefixProd)`, fixing one child
  edge `(u, v)`.
* `mem_edgeListParLiftChild` — combines `mem_edgeListParLiftOne`
  over a list of child edges.
* `mem_edgeListParGo_nil`, `mem_edgeListParGo_cons` — top-level
  recursion over the children list.
* `mem_edgeListPar` — the `prefixProd = 1` corollary that connects
  to `edgeList (par ss)`.

Why we need this module. The `par`-case proofs in
`Reticulate.Spec.Reachability` need to (a) lift child reachability
into the product graph and (b) unlift product reachability back
into per-child reachability. Both directions reduce to "given an
edge in the product, find the unique child + the prefix and suffix
indices that produced it" — which is exactly what these
characterisations provide.

Conceptual dependencies.
* `Reticulate.Spec.StateSpace` for the four helpers and
  `prodChildren`.
-/

namespace Reticulate.Spec

namespace SessionType

open edgeList

/-! ## Lemma 1 — `mem_edgeListParLiftSuffix` -/

/-- Membership-rewrite for the innermost `par`-builder layer.

An edge `(src, tgt)` is emitted by `edgeListParLiftSuffix` exactly
when there is a suffix-coordinate `q ∈ [q0, suffixProd)` whose
corresponding componentwise pair matches `(src, tgt)`.

Used by `mem_edgeListParLiftOne` to assemble the next layer up.
Proof technique: strong induction on `suffixProd - q0`. -/
theorem mem_edgeListParLiftSuffix
    (u v start suffixProd size pBase q0 : Nat) (src tgt : Nat) :
    (src, tgt) ∈ edgeListParLiftSuffix u v start suffixProd size pBase q0
      ↔ ∃ q, q0 ≤ q ∧ q < suffixProd ∧
             src = start + pBase + u * suffixProd + q ∧
             tgt = start + pBase + v * suffixProd + q := by
  -- Strong induction on `suffixProd - q0`.
  induction h : suffixProd - q0 using Nat.strong_induction_on generalizing q0 with
  | _ n ih =>
    subst h
    unfold edgeListParLiftSuffix
    split
    · rename_i hq
      -- `q0 < suffixProd`: cons of head pair plus recursive call at `q0 + 1`.
      simp only [List.mem_cons]
      constructor
      · rintro (heq | hrec)
        · -- head case: `(src, tgt) = (start+..+u*..+q0, start+..+v*..+q0)`
          refine ⟨q0, Nat.le_refl _, hq, ?_, ?_⟩
          · exact (Prod.mk.injEq _ _ _ _).mp heq |>.1
          · exact (Prod.mk.injEq _ _ _ _).mp heq |>.2
        · -- recursive case
          have : suffixProd - (q0 + 1) < suffixProd - q0 := by omega
          rcases (ih _ this (q0 + 1) rfl).mp hrec with ⟨q, hq0, hqlt, hsrc, htgt⟩
          exact ⟨q, Nat.le_of_succ_le hq0, hqlt, hsrc, htgt⟩
      · rintro ⟨q, hq0, hqlt, hsrc, htgt⟩
        by_cases hq_eq : q = q0
        · left
          subst hq_eq
          subst hsrc
          subst htgt
          rfl
        · right
          have hq_gt : q0 + 1 ≤ q := by
            rcases Nat.lt_or_ge q0 q with hlt | hge
            · omega
            · omega
          have : suffixProd - (q0 + 1) < suffixProd - q0 := by omega
          exact (ih _ this (q0 + 1) rfl).mpr ⟨q, hq_gt, hqlt, hsrc, htgt⟩
    · rename_i hq
      -- `¬ q0 < suffixProd`: empty list; RHS should be vacuous.
      simp only [List.not_mem_nil, false_iff]
      rintro ⟨q, hq0, hqlt, _, _⟩
      omega

/-! ## Lemma 2 — `mem_edgeListParLiftOne` -/

/-- Membership-rewrite for the middle `par`-builder layer.

An edge `(src, tgt)` is in `edgeListParLiftOne u v …` exactly when
there exist a prefix-coordinate `p ∈ [p0, prefixProd)` and a
suffix-coordinate `q ∈ [0, suffixProd)` whose componentwise pair
gives `(src, tgt)`.

Proof technique: strong induction on `prefixProd - p0`, using
`mem_edgeListParLiftSuffix` at the `p = p0` head case. -/
theorem mem_edgeListParLiftOne
    (u v start suffixProd size prefixProd p0 : Nat) (src tgt : Nat) :
    (src, tgt) ∈ edgeListParLiftOne u v start suffixProd size prefixProd p0
      ↔ ∃ p q, p0 ≤ p ∧ p < prefixProd ∧ q < suffixProd ∧
               src = start + p * (size * suffixProd) + u * suffixProd + q ∧
               tgt = start + p * (size * suffixProd) + v * suffixProd + q := by
  induction h : prefixProd - p0 using Nat.strong_induction_on generalizing p0 with
  | _ n ih =>
    subst h
    unfold edgeListParLiftOne
    split
    · rename_i hp
      -- `p0 < prefixProd`: append of `Suffix(p0)` and recursive call.
      simp only [List.mem_append]
      constructor
      · rintro (hhead | hrec)
        · -- from head: a `q` witness for current `p = p0`
          rcases (mem_edgeListParLiftSuffix u v start suffixProd size
                    (p0 * (size * suffixProd)) 0 src tgt).mp hhead with
            ⟨q, _, hqlt, hsrc, htgt⟩
          exact ⟨p0, q, Nat.le_refl _, hp, hqlt, hsrc, htgt⟩
        · have hdec : prefixProd - (p0 + 1) < prefixProd - p0 := by omega
          rcases (ih _ hdec (p0 + 1) rfl).mp hrec with
            ⟨p, q, hp0, hplt, hqlt, hsrc, htgt⟩
          exact ⟨p, q, Nat.le_of_succ_le hp0, hplt, hqlt, hsrc, htgt⟩
      · rintro ⟨p, q, hp0, hplt, hqlt, hsrc, htgt⟩
        by_cases hp_eq : p = p0
        · left
          subst hp_eq
          exact (mem_edgeListParLiftSuffix u v start suffixProd size
                   (p * (size * suffixProd)) 0 src tgt).mpr
                 ⟨q, Nat.zero_le _, hqlt, hsrc, htgt⟩
        · right
          have hp_gt : p0 + 1 ≤ p := by
            rcases Nat.lt_or_ge p0 p with hlt | hge
            · omega
            · omega
          have hdec : prefixProd - (p0 + 1) < prefixProd - p0 := by omega
          exact (ih _ hdec (p0 + 1) rfl).mpr
                 ⟨p, q, hp_gt, hplt, hqlt, hsrc, htgt⟩
    · rename_i hp
      -- `¬ p0 < prefixProd`: empty.
      simp only [List.not_mem_nil, false_iff]
      rintro ⟨p, q, hp0, hplt, _, _, _⟩
      omega

/-! ## Lemma 3 — `mem_edgeListParLiftChild` -/

/-- Membership-rewrite for the per-child lifting layer.

An edge `(src, tgt)` is emitted by `edgeListParLiftChild` from a
list of child-local edges `edges` exactly when some child edge
`(u, v) ∈ edges` and some `(p, q)` together produce
`(src, tgt)` under the row-major encoding.

Proof technique: induction on the edge list, with the head case
delegated to `mem_edgeListParLiftOne`. -/
theorem mem_edgeListParLiftChild
    (edges : List (Nat × Nat)) (start suffixProd size prefixProd : Nat)
    (src tgt : Nat) :
    (src, tgt) ∈ edgeListParLiftChild edges start suffixProd size prefixProd
      ↔ ∃ u v, (u, v) ∈ edges ∧
               ∃ p q, p < prefixProd ∧ q < suffixProd ∧
                      src = start + p * (size * suffixProd) + u * suffixProd + q ∧
                      tgt = start + p * (size * suffixProd) + v * suffixProd + q := by
  induction edges with
  | nil =>
    unfold edgeListParLiftChild
    simp only [List.not_mem_nil, false_and, exists_const]
  | cons e tl ih =>
    rcases e with ⟨u0, v0⟩
    unfold edgeListParLiftChild
    simp only [List.mem_append, List.mem_cons, Prod.mk.injEq]
    constructor
    · rintro (hhead | hrest)
      · rcases (mem_edgeListParLiftOne u0 v0 start suffixProd size prefixProd 0
                  src tgt).mp hhead with ⟨p, q, _, hplt, hqlt, hsrc, htgt⟩
        exact ⟨u0, v0, Or.inl ⟨rfl, rfl⟩, p, q, hplt, hqlt, hsrc, htgt⟩
      · rcases ih.mp hrest with ⟨u, v, hmem, p, q, hplt, hqlt, hsrc, htgt⟩
        exact ⟨u, v, Or.inr hmem, p, q, hplt, hqlt, hsrc, htgt⟩
    · rintro ⟨u, v, hmem, p, q, hplt, hqlt, hsrc, htgt⟩
      rcases hmem with ⟨hu, hv⟩ | hmem
      · left
        subst hu; subst hv
        exact (mem_edgeListParLiftOne u v start suffixProd size prefixProd 0
                 src tgt).mpr ⟨p, q, Nat.zero_le _, hplt, hqlt, hsrc, htgt⟩
      · right
        exact ih.mpr ⟨u, v, hmem, p, q, hplt, hqlt, hsrc, htgt⟩

/-! ## Lemma 4 — `mem_edgeListParGo` (recursive form)

We use the recursive variant suggested in the brief: an edge belongs to
`edgeListParGo (s :: tl) start env prefixProd` iff it is either

* the lift of a filtered local edge of the head child `s`, across the
  prefix `[0, prefixProd)` and suffix `[0, prodChildren tl)`, or
* an edge of `edgeListParGo tl start env (prefixProd * stateCount s)`. -/

/-- Membership-rewrite for `edgeListParGo` on the empty children
list: the result is empty, so no edge belongs. Base case for
`mem_edgeListParGo_cons`. Proof technique: unfold and `simp`. -/
theorem mem_edgeListParGo_nil
    (start : Nat) (env : List (String × Nat)) (prefixProd : Nat)
    (src tgt : Nat) :
    (src, tgt) ∈ edgeListParGo ([] : List SessionType) start env prefixProd
      ↔ False := by
  rw [edgeListParGo.eq_def]
  simp

/-- Membership-rewrite for `edgeListParGo` on a non-empty children
list `s :: tl`: an edge belongs iff it comes from the head child's
filtered local edges (lifted across the current prefix and the
remaining children's suffix product), or from the recursive call
on the tail with `prefixProd` extended by `stateCount s`.

Top of the helper-stack used by `Reticulate.Spec.Reachability` to
unfold `par`-edge membership. Proof technique: unfold and
`simp [List.mem_append]`. -/
theorem mem_edgeListParGo_cons
    (s : SessionType) (tl : List SessionType) (start : Nat)
    (env : List (String × Nat)) (prefixProd : Nat)
    (src tgt : Nat) :
    (src, tgt) ∈ edgeListParGo (s :: tl) start env prefixProd
      ↔ ( let size := stateCount s
          let suffixProd := stateCount.prodChildren tl
          let rawChild := edgeList s 0 env
          let localEdges :=
            rawChild.filter (fun e => decide (e.1 < size) && decide (e.2 < size))
          (src, tgt) ∈ edgeListParLiftChild localEdges start suffixProd size prefixProd )
        ∨ (src, tgt) ∈ edgeListParGo tl start env (prefixProd * stateCount s) := by
  rw [edgeListParGo.eq_def]
  simp only [List.mem_append]

/-! ## Lemma 5 — `mem_edgeListPar` corollary -/

/-- The top-level wrapper: `edgeListPar ss start env` equals
`edgeListParGo ss start env 1`, so membership is the same.

This is the connector between the public `edgeListPar` (used by
`edgeList (par ss)`) and the recursive analysis given by
`mem_edgeListParGo_cons`. Proof: definitional unfolding. -/
theorem mem_edgeListPar
    (ss : List SessionType) (start : Nat) (env : List (String × Nat))
    (src tgt : Nat) :
    (src, tgt) ∈ edgeListPar ss start env
      ↔ (src, tgt) ∈ edgeListParGo ss start env 1 := by
  unfold edgeListPar
  exact Iff.rfl

end SessionType

end Reticulate.Spec
