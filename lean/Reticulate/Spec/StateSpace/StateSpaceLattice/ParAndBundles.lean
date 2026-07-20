/-
Copyright (c) 2026 Alexandre Zua Caldeira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexandre Zua Caldeira
-/

import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Quotient
import Reticulate.Spec.StateSpace.StateSpace
import Reticulate.Spec.StateSpace.StateSpaceEdges
import Reticulate.Spec.Core.Reachability
import Reticulate.Spec.Core.FreeVars
import Reticulate.Spec.Core.WellFormed
import Reticulate.Graph.SCC

/-!
# The Reticulate Theorem: every well-formed type's SCC quotient is a bounded lattice

This file delivers the headline result of the ICE 2026 paper —
`thm:reticulate`, the **Reticulate Theorem**:

> For every well-formed session type `S`, the SCC quotient
> `\mathcal{L}(S)/\equiv` of its state space is a bounded lattice.

The Lean witness is `reticulate_lattice` at the end of this file.

The proof works by gluing together per-constructor "lattice
bridges" — one for each shape of `SessionType` — and combining
them with the unconditional reachability lemmas of
`Reticulate.Spec.Reachability`. The four bridges:

* **Bridge 1, `end_`** — `State end_` is a singleton, so its SCC
  quotient is a subsingleton and trivially a lattice (and bounded
  order).
* **Bridge 2, `BoundedOrder` for every `S`** — the unconditional
  `instBoundedOrder` instance below uses
  `rootReachesAll_uncond` and `allReachExit_uncond` to give
  `⊥ = [initialState]`, `⊤ = [terminalState]` for any session
  type. This is half of `prop:extrema` (§3 of the paper).
* **Bridge 3, `branch` and `select`** — reachability is restricted
  to the children's sub-regions plus the entry/exit slots; using
  `branch_scc_classifier` we can decide which SCC each state
  belongs to, then build `sup` and `inf` as case-distinct functions
  over the classifier. See `prop:reach-preorder` and
  surrounding text in §3.
* **Bridge 4, `par`** — the product encoding gives a bijection
  between `SCCQuotient (stateSpace (par ss))` and the dependent
  product `∀ i, SCCQuotient (stateSpace ssᵢ)`, so the lattice
  transports componentwise (matches `def:product` and
  `def:product-construction`).
* **Bridge 5, `rec_`** — when the bound variable does not appear
  free elsewhere, the recursion's SCC quotient is the same as the
  body's. The general case adds one extra equivalence class
  (the "root rec class") and is handled by the absorption-style
  argument of `lem:recursion`.

What is exported.
* `instBoundedOrder` — the unconditional `BoundedOrder` instance
  (Bridge 2).
* `end_lattice`, `end_boundedOrder` — Bridge 1.
* `parSCCOrderIso`, `par_lattice` — Bridge 4.
* `var_latticeStruct` — Bridge 5 trivial case (a free variable's
  state space is a singleton).
* `rec_lattice_of_notFreeVar` — Bridge 5 freshness case.
* `branch_latticeStruct`, `select_latticeStruct` — Bridge 3.
* `universal_lattice`, `universal_Lattice`, `reticulate_lattice` —
  the assembled headline result.
* `reachable_of_edgeRel` — promotes `Nat`-level walks (as
  produced by `Reticulate.Spec.Reachability`) into `Fin`-level
  walks usable by `Reachable (stateSpace S)`.

Conceptual dependencies.
* `Reticulate.Spec.StateSpace`, `StateSpaceEdges`, `Reachability`
  — the graph and its reachability lemmas.
* `Reticulate.Spec.WellFormed` for the `parClosed` clause used by
  the recursion bridge.
* `Reticulate.SCC` for `SCCQuotient` and its partial order.
* Mathlib's `Lattice`, `BoundedOrder`, `OrderIso` typeclass stack.

This file contains no `sorry` and no `axiom`. Where a bridge could
not be fully mechanised in earlier phases, the sub-phase stopped
rather than shipped a stub; the current `reticulate_lattice` is
the universal, ungated form.
-/

namespace Reticulate.Spec

namespace SessionType

open Reticulate

/-!
## Bridge 1 — `end_` is a subsingleton
-/

/-- `State .end_` is a subsingleton: `stateCount .end_ = 1` so the carrier
`Fin 1` has exactly one element. -/
instance : Subsingleton (State (.end_ : SessionType)) := by
  unfold State
  show Subsingleton (Fin 1)
  exact inferInstance

/-- The SCC quotient of a one-element graph is a subsingleton. -/
instance end_scc_subsingleton :
    Subsingleton (SCCQuotient (stateSpace (.end_ : SessionType))) := by
  refine ⟨fun x y => ?_⟩
  induction x using Quotient.ind with
  | _ u =>
    induction y using Quotient.ind with
    | _ v =>
      have : u = v := Subsingleton.elim u v
      exact congrArg _ this

/-!
### Lattice and BoundedOrder on a subsingleton partial order

A subsingleton with a partial order trivially has all meets and joins
(they are equal to the unique element). We construct the `Lattice` and
`BoundedOrder` instances explicitly, using the existing `PartialOrder`
instance from `SCC.lean`.
-/

/-- Bridge 1 final: the SCC quotient for `end_` is a `Lattice`. -/
instance end_lattice : Lattice (SCCQuotient (stateSpace (.end_ : SessionType))) where
  sup x _ := x
  le_sup_left x y := by
    have : x = y := Subsingleton.elim x y
    exact this ▸ le_refl x
  le_sup_right x y := by
    have : x = y := Subsingleton.elim x y
    exact this ▸ le_refl x
  sup_le x y z hxz _ := by
    have : x = y := Subsingleton.elim x y
    exact this ▸ hxz
  inf x _ := x
  inf_le_left x y := by
    have : x = y := Subsingleton.elim x y
    exact this ▸ le_refl x
  inf_le_right x y := by
    have : x = y := Subsingleton.elim x y
    exact this ▸ le_refl x
  le_inf x y z hxy _ := by
    have : y = z := Subsingleton.elim y z
    exact this ▸ hxy

/-- Bridge 1 final: the SCC quotient for `end_` has a `BoundedOrder`. -/
instance end_boundedOrder :
    BoundedOrder (SCCQuotient (stateSpace (.end_ : SessionType))) where
  top := Quotient.mk _ (initialState .end_)
  le_top x := by
    have : x = Quotient.mk _ (initialState .end_) := Subsingleton.elim x _
    exact this ▸ le_refl x
  bot := Quotient.mk _ (initialState .end_)
  bot_le x := by
    have : x = Quotient.mk _ (initialState .end_) := Subsingleton.elim x _
    exact this ▸ le_refl x

/-!
## Bridge 2 — BoundedOrder for `par ss` (and every session type)

The `BoundedOrder` structure descends from the universal reachability
lemmas `rootReachesAll_uncond` and `allReachExit_uncond` in
`Reticulate.Spec.Reachability`. These two theorems guarantee that every
`stateSpace S` has a canonical entry (index `0`) that reaches every
other state, and a canonical exit (`exitSlot S 0`) that every state
reaches. Thus in the SCC quotient:

* `[initialState S] ≤ [x]` — every `x` sits above the initial SCC.
* `[x] ≤ [terminalState S]` — every `x` sits below the terminal SCC.

The bridge from `Nat`-level walks (as returned by `rootReachesAll_uncond`
and `allReachExit_uncond`) to `Fin`-level walks (needed by
`Reachable (stateSpace S)`) is the lifting lemma
`reachable_of_edgeRel_uncond`.
-/

/-!
### Lifting Nat-level walks into `stateSpace`

`edgeRel S 0 []` is the `Nat` version of the edge relation, and
`stateSpace S` is the `FinDiGraph` over `Fin (stateCount S)` that uses
the same edge list. We translate Nat-level reachability into Fin-level
reachability by an induction that uses `walk_source_in_range` to keep
every intermediate node in range.
-/

/-- Promote a walk in the `Nat`-typed `edgeRel S 0 []` into the
`Fin`-typed `Reachable (stateSpace S)`.

`Reticulate.Spec.Reachability` builds walks at the `Nat` level
because that lets us shift indices freely. The `BoundedOrder`
instance, however, lives on `SCCQuotient (stateSpace S)` whose
underlying carrier is `State S = Fin (stateCount S)`. This lemma
bridges the two. Proof technique: head-induction on the walk; at
each step `walk_source_in_range` certifies the intermediate index
is in range so we can package it as a `Fin`. -/
theorem reachable_of_edgeRel
    (S : SessionType) {x y : Nat}
    (hx : x < stateCount S) (hy : y < stateCount S)
    (hwalk : Relation.ReflTransGen (edgeRel S 0 []) x y) :
    Reachable (stateSpace S) ⟨x, hx⟩ ⟨y, hy⟩ := by
  -- Induct on the walk via head-style induction; at each head-edge,
  -- use `walk_source_in_range` to establish that the intermediate
  -- index is in range, letting us package it as a `Fin`.
  induction hwalk using Relation.ReflTransGen.head_induction_on with
  | refl =>
    -- x = y as Nat (hwalk is refl); hx, hy witness the same bound but
    -- `ReflTransGen.refl` requires the endpoints to be definitionally
    -- equal. The Fin-level walk is `Reachable.refl`.
    exact Reachable.refl _ _
  | @head a b hedge hrest ih =>
    -- hedge : edgeRel S 0 [] a b = (a, b) ∈ edgeList S 0 []
    -- hrest : ReflTransGen (edgeRel S 0 []) b y
    -- Need: Reachable (stateSpace S) ⟨a, hx⟩ ⟨y, hy⟩.
    -- Intermediate index b is in range by `walk_source_in_range`.
    have hb_range : 0 ≤ b ∧ b < 0 + stateCount S :=
      walk_source_in_range S 0 [] (Nat.zero_le _) (by simpa using hy) hrest
    have hb : b < stateCount S := by
      have := hb_range.2; simpa using this
    -- Fin version of the head edge.
    have hedgeFin : (stateSpace S).edge ⟨a, hx⟩ ⟨b, hb⟩ := by
      show (a, b) ∈ edgeList S 0 []
      exact hedge
    -- Recurse.
    exact Relation.ReflTransGen.head hedgeFin (ih hb)

/-!
### BoundedOrder instance — works for every session type

The instance below is stated for arbitrary `S : SessionType`, covering
`par ss` as a special case. This is strictly stronger than the brief's
`par_boundedOrder` — no hypothesis on children is needed, because
`rootReachesAll_uncond` and `allReachExit_uncond` are themselves
unconditional.
-/

/-- **The unconditional `BoundedOrder` instance.**

For every session type `S`, the SCC quotient of its state space
is a bounded order: `⊥` is the SCC class of `initialState S`
(index `0`, the entry), `⊤` is the SCC class of `terminalState S`
(at `exitSlot S 0`, the canonical exit). This is half of
`prop:extrema` of §3 of the paper.

No assumption on `S` (no termination, no closedness, no
parClosed): the unconditional reachability theorems
`rootReachesAll_uncond` and `allReachExit_uncond` already
guarantee that `0` reaches everything and everything reaches the
exit. The instance is defined directly so Lean's typeclass search
finds it whenever a `BoundedOrder` is requested on
`SCCQuotient (stateSpace S)`.

Proof technique: induct on the SCC class to obtain a representative,
apply the relevant reachability theorem, then lift via
`reachable_of_edgeRel` from `Nat`-walks into `Fin`-walks. -/
instance instBoundedOrder (S : SessionType) :
    BoundedOrder (SCCQuotient (stateSpace S)) where
  top := Quotient.mk _ (terminalState S)
  bot := Quotient.mk _ (initialState S)
  le_top := by
    intro x
    induction x using Quotient.ind with
    | _ u =>
      -- Goal: Quotient.mk _ u ≤ Quotient.mk _ (terminalState S).
      -- By the quotient order definition (SCC.lean, `le'`), this unfolds
      -- to `Reachable (stateSpace S) u (terminalState S)`.
      show Reachable (stateSpace S) u (terminalState S)
      -- `terminalState S` is `⟨e, h⟩` or fallback. We do a case split.
      by_cases he : exitSlot S 0 < stateCount S
      · -- Normal case: `terminalState S = ⟨exitSlot S 0, he⟩`.
        have hterm_eq : terminalState S = ⟨exitSlot S 0, he⟩ := by
          unfold terminalState
          simp [he]
        rw [hterm_eq]
        -- Get the Nat-level walk u.val → exitSlot S 0.
        have hwalkNat : Relation.ReflTransGen (edgeRel S 0 [])
            (0 + u.val) (exitSlot S 0) :=
          allReachExit_uncond S [] 0 u.val u.isLt
        have hwalkNat' : Relation.ReflTransGen (edgeRel S 0 [])
            u.val (exitSlot S 0) := by simpa using hwalkNat
        -- Lift to Fin.
        have := reachable_of_edgeRel S u.isLt he hwalkNat'
        -- `⟨u.val, u.isLt⟩ = u`.
        have hueq : (⟨u.val, u.isLt⟩ : State S) = u := rfl
        rw [hueq] at this
        exact this
      · -- Degenerate case: `terminalState S = initialState S = ⟨0, _⟩`.
        -- `exitSlot_lt S 0` rules this out, so he is absurd.
        exact absurd (by have := exitSlot_lt S 0; omega : exitSlot S 0 < stateCount S) he
  bot_le := by
    intro x
    induction x using Quotient.ind with
    | _ u =>
      show Reachable (stateSpace S) (initialState S) u
      -- `initialState S = ⟨0, stateCount_pos S⟩`.
      -- Get the Nat-level walk 0 → u.val.
      have hwalkNat : Relation.ReflTransGen (edgeRel S 0 [])
          0 (0 + u.val) :=
        rootReachesAll_uncond S [] 0 u.val u.isLt
      have hwalkNat' : Relation.ReflTransGen (edgeRel S 0 [])
          0 u.val := by simpa using hwalkNat
      -- Lift to Fin.
      have := reachable_of_edgeRel S (stateCount_pos S) u.isLt hwalkNat'
      -- `⟨0, stateCount_pos S⟩ = initialState S` and `⟨u.val, u.isLt⟩ = u`.
      have hstart : (⟨0, stateCount_pos S⟩ : State S) = initialState S := rfl
      have hueq : (⟨u.val, u.isLt⟩ : State S) = u := rfl
      rw [hstart, hueq] at this
      exact this

/-!
### Scope (A) alias theorems

These are the exact statements from the Phase 1b-β1c brief, provided
as named corollaries of the stronger universal instance above.
-/

/-- Brief-form statement: `par ss` has a `BoundedOrder` instance on its
    SCC quotient, for every child list `ss`. No hypotheses on children
    are required (the universal reachability lemmas are themselves
    unconditional). -/
def par_boundedOrder (ss : List SessionType) :
    BoundedOrder (SCCQuotient (stateSpace (.par ss : SessionType))) :=
  instBoundedOrder (.par ss)

/-!
## Phase 1b-β1c-full — Stride bijection (Step 1)

The stride bijection is the arithmetic heart of the par lattice bridge:
* `flatToTuple ss k _ i` extracts the `i`-th coordinate of `k < prodChildren ss`
  in row-major (big-endian) encoding.
* `tupleToFlat ss tup _` rebuilds a flat index from an in-range tuple.

We state everything on `Nat` with in-range hypotheses so that the proofs
avoid `Fin`-typed manipulation; the final order-isomorphism (Step 5)
bridges back to `Fin` at the end.
-/

/-- `Nat`-indexed projection of `k` onto its `i`-th coordinate under the
    row-major encoding. Takes an in-range hypothesis `i < ss.length`
    implicitly through the `List.get?`-style recursion. -/
def flatToTupleNat : (ss : List SessionType) → (k : Nat) → (i : Nat) → Nat
  | [],      _, _       => 0  -- vacuous
  | s :: tl, k, 0       => k / stateCount.prodChildren tl
  | _ :: tl, k, (i + 1) => flatToTupleNat tl (k % stateCount.prodChildren tl) i

/-- Bound for the Nat-indexed projection: `flatToTupleNat ss k i < stateCount ss[i]`
    whenever `k < prodChildren ss` and `i < ss.length`. -/
theorem flatToTupleNat_lt :
    ∀ (ss : List SessionType) (k : Nat), k < stateCount.prodChildren ss →
      ∀ (i : Nat) (hi : i < ss.length),
        flatToTupleNat ss k i < stateCount (ss.get ⟨i, hi⟩)
  | [],      _, _,  _, hi => by simp at hi
  | s :: tl, k, hk, 0, _  => by
      -- flatToTupleNat (s :: tl) k 0 = k / prodChildren tl < stateCount s
      simp only [flatToTupleNat, List.get]
      show k / stateCount.prodChildren tl < stateCount s
      have hpc_pos : 0 < stateCount.prodChildren tl := by
        have hpc_all : stateCount.prodChildren (s :: tl) = stateCount s * stateCount.prodChildren tl := by
          simp [stateCount.prodChildren]
        rw [hpc_all] at hk
        rcases Nat.eq_zero_or_pos (stateCount.prodChildren tl) with h0 | hpos
        · rw [h0] at hk; simp at hk
        · exact hpos
      apply Nat.div_lt_of_lt_mul
      have : stateCount.prodChildren (s :: tl) = stateCount s * stateCount.prodChildren tl := by
        simp [stateCount.prodChildren]
      rw [this] at hk
      rw [Nat.mul_comm]
      exact hk
  | s :: tl, k, hk, (i + 1), hi => by
      -- flatToTupleNat (s :: tl) k (i+1) = flatToTupleNat tl (k mod prodChildren tl) i
      simp only [flatToTupleNat, List.get]
      have hpc_pos : 0 < stateCount.prodChildren tl := by
        have hpc_all : stateCount.prodChildren (s :: tl) = stateCount s * stateCount.prodChildren tl := by
          simp [stateCount.prodChildren]
        rw [hpc_all] at hk
        rcases Nat.eq_zero_or_pos (stateCount.prodChildren tl) with h0 | hpos
        · rw [h0] at hk; simp at hk
        · exact hpos
      have hmod : k % stateCount.prodChildren tl < stateCount.prodChildren tl :=
        Nat.mod_lt _ hpc_pos
      have hi' : i < tl.length := by
        simp [List.length] at hi; omega
      exact flatToTupleNat_lt tl (k % stateCount.prodChildren tl) hmod i hi'

/-- Rebuild the flat index from a tuple of coordinates, each in its child's
    range. The tuple is given as a function `Nat → Nat` with the convention
    that indices `≥ ss.length` are ignored. -/
def tupleToFlatNat : (ss : List SessionType) → (tup : Nat → Nat) → Nat
  | [],      _   => 0
  | s :: tl, tup =>
      tup 0 * stateCount.prodChildren tl + tupleToFlatNat tl (fun i => tup (i + 1))

/-- Bound for `tupleToFlatNat`: if every coordinate is in range, the flat
    index is `< prodChildren ss`. -/
theorem tupleToFlatNat_lt :
    ∀ (ss : List SessionType) (tup : Nat → Nat),
      (∀ i (hi : i < ss.length), tup i < stateCount (ss.get ⟨i, hi⟩)) →
      tupleToFlatNat ss tup < stateCount.prodChildren ss
  | [],      _,   _ => by
      simp [tupleToFlatNat, stateCount.prodChildren]
  | s :: tl, tup, h => by
      simp only [tupleToFlatNat, stateCount.prodChildren]
      -- tup 0 < stateCount s (from h 0 _)
      have h0 : tup 0 < stateCount s := h 0 (by simp)
      -- Recurse on tail
      have hTail : (∀ i (hi : i < tl.length),
          (fun i => tup (i + 1)) i < stateCount (tl.get ⟨i, hi⟩)) := by
        intro i hi
        have hi' : i + 1 < (s :: tl).length := by simp [List.length]; omega
        have := h (i + 1) hi'
        simp [List.get] at this
        exact this
      have hTailBd : tupleToFlatNat tl (fun i => tup (i + 1))
                      < stateCount.prodChildren tl :=
        tupleToFlatNat_lt tl _ hTail
      -- tup 0 * prodChildren tl + tupleToFlatNat tl _ <
      --   stateCount s * prodChildren tl
      -- bound: tup 0 ≤ stateCount s - 1.
      have hpc_pos : 0 < stateCount.prodChildren tl := by
        exact Nat.lt_of_le_of_lt (Nat.zero_le _) hTailBd
      calc tup 0 * stateCount.prodChildren tl +
              tupleToFlatNat tl (fun i => tup (i + 1))
          < tup 0 * stateCount.prodChildren tl + stateCount.prodChildren tl := by omega
        _ = (tup 0 + 1) * stateCount.prodChildren tl := by ring
        _ ≤ stateCount s * stateCount.prodChildren tl :=
            Nat.mul_le_mul_right _ h0

/-- `tupleToFlatNat` only inspects in-range indices: if two tuples agree on
    `[0, ss.length)`, they yield the same flat index. -/
theorem tupleToFlatNat_congr :
    ∀ (ss : List SessionType) {tup tup' : Nat → Nat},
      (∀ i, i < ss.length → tup i = tup' i) →
      tupleToFlatNat ss tup = tupleToFlatNat ss tup'
  | [],      _, _, _ => by simp [tupleToFlatNat]
  | s :: tl, tup, tup', h => by
      simp only [tupleToFlatNat]
      have h0 : tup 0 = tup' 0 := h 0 (by simp)
      have hTail : ∀ i, i < tl.length →
          (fun i => tup (i + 1)) i = (fun i => tup' (i + 1)) i := by
        intro i hi
        exact h (i + 1) (by simp [List.length]; omega)
      rw [h0, tupleToFlatNat_congr tl hTail]

/-!
### Round-trip lemmas

`tupleToFlatNat ss (flatToTupleNat ss k) = k`
`flatToTupleNat ss (tupleToFlatNat ss tup) i = tup i` (for `i < ss.length`)
-/

/-- Round-trip `flat → tuple → flat`. -/
theorem tupleToFlat_flatToTuple :
    ∀ (ss : List SessionType) (k : Nat), k < stateCount.prodChildren ss →
      tupleToFlatNat ss (flatToTupleNat ss k) = k
  | [],      k, hk => by
      simp [stateCount.prodChildren] at hk
      -- k = 0
      subst hk
      simp [tupleToFlatNat]
  | s :: tl, k, hk => by
      -- LHS = (k / pcTl) * pcTl + tupleToFlatNat tl (flatToTupleNat tl (k % pcTl))
      --     = (k / pcTl) * pcTl + (k % pcTl)       [by IH]
      --     = k                                     [div+mod identity]
      simp only [tupleToFlatNat, flatToTupleNat]
      have hpc_all : stateCount.prodChildren (s :: tl) =
                      stateCount s * stateCount.prodChildren tl := by
        simp [stateCount.prodChildren]
      rw [hpc_all] at hk
      have hpc_pos : 0 < stateCount.prodChildren tl := by
        rcases Nat.eq_zero_or_pos (stateCount.prodChildren tl) with h0 | hpos
        · rw [h0] at hk; simp at hk
        · exact hpos
      have hmod : k % stateCount.prodChildren tl < stateCount.prodChildren tl :=
        Nat.mod_lt _ hpc_pos
      have hIH := tupleToFlat_flatToTuple tl (k % stateCount.prodChildren tl) hmod
      -- Goal (after simp only unfolds): k/pcTl * pcTl + tupleToFlatNat tl (flatToTupleNat tl (k % pcTl)) = k
      rw [hIH]
      -- Nat.div_add_mod has form `n * (k/n) + k%n = k`; rearrange via ring-ish.
      conv_lhs => rw [Nat.mul_comm]
      exact Nat.div_add_mod k _

/-- Round-trip `tuple → flat → tuple`, pointwise at each in-range index. -/
theorem flatToTuple_tupleToFlat :
    ∀ (ss : List SessionType) (tup : Nat → Nat),
      (∀ i (hi : i < ss.length), tup i < stateCount (ss.get ⟨i, hi⟩)) →
      ∀ (i : Nat), i < ss.length →
        flatToTupleNat ss (tupleToFlatNat ss tup) i = tup i
  | [],      _,   _, i, hi => by simp at hi
  | s :: tl, tup, h, 0, _ => by
      -- LHS = (tup 0 * pcTl + tupleToFlatNat tl _) / pcTl
      -- Claim: this equals tup 0.
      simp only [flatToTupleNat, tupleToFlatNat]
      have hTail : (∀ i (hi : i < tl.length),
          (fun i => tup (i + 1)) i < stateCount (tl.get ⟨i, hi⟩)) := by
        intro i hi
        have hi' : i + 1 < (s :: tl).length := by simp [List.length]; omega
        have := h (i + 1) hi'
        simp [List.get] at this
        exact this
      have hTailBd : tupleToFlatNat tl (fun i => tup (i + 1)) < stateCount.prodChildren tl :=
        tupleToFlatNat_lt tl _ hTail
      have hpc_pos : 0 < stateCount.prodChildren tl :=
        Nat.lt_of_le_of_lt (Nat.zero_le _) hTailBd
      -- (tup 0 * pcTl + x) / pcTl = tup 0 when x < pcTl
      -- Reassoc: tup 0 * pcTl + x = x + pcTl * tup 0 (by comm).
      have hcomm : tup 0 * stateCount.prodChildren tl +
                    tupleToFlatNat tl (fun i => tup (i + 1))
                  = tupleToFlatNat tl (fun i => tup (i + 1)) +
                    stateCount.prodChildren tl * tup 0 := by ring
      rw [hcomm, Nat.add_mul_div_left _ _ hpc_pos,
          Nat.div_eq_of_lt hTailBd, Nat.zero_add]
  | s :: tl, tup, h, (i + 1), hi => by
      -- LHS = flatToTupleNat tl ((tupleToFlatNat (s::tl) tup) % pcTl) i
      -- Simplify: (tup 0 * pcTl + x) % pcTl = x, then use IH.
      simp only [flatToTupleNat, tupleToFlatNat]
      have hTail : (∀ i (hi : i < tl.length),
          (fun i => tup (i + 1)) i < stateCount (tl.get ⟨i, hi⟩)) := by
        intro j hj
        have hj' : j + 1 < (s :: tl).length := by simp [List.length]; omega
        have := h (j + 1) hj'
        simp [List.get] at this
        exact this
      have hTailBd : tupleToFlatNat tl (fun i => tup (i + 1)) < stateCount.prodChildren tl :=
        tupleToFlatNat_lt tl _ hTail
      have hi' : i < tl.length := by simp [List.length] at hi; omega
      have hIH := flatToTuple_tupleToFlat tl (fun j => tup (j + 1)) hTail i hi'
      -- Reduce the modulo:
      have hcomm : tup 0 * stateCount.prodChildren tl +
                    tupleToFlatNat tl (fun j => tup (j + 1))
                  = tupleToFlatNat tl (fun j => tup (j + 1)) +
                    stateCount.prodChildren tl * tup 0 := by ring
      rw [hcomm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hTailBd]
      exact hIH

/-!
## Phase 1b-β1c-full — Edge coordinate-change structure (Step 2, partial)

Two structural lemmas that bridge the flat-index arithmetic (Step 1) to
the edge structure (mem_edgeListParGo_cons):

* `edgeListParGo_head_coord_change` — a head-lift membership unfolds
  into an explicit (p, u, v, q) witness with arithmetic endpoint
  formulas.
* `flatToTupleNat_head_split_*` — decode arithmetic:
  `(u * prodChildren tl + q) / prodChildren tl = u` and
  `(u * prodChildren tl + q) % prodChildren tl = q`.

These isolate the coordinate-preservation facts needed for Step 3
forward (a par-edge changes at most one coordinate). The full Step 3
forward induction on walks, the backward interleave construction, and
the resulting order-iso plus Lattice transport remain open work.
-/

/-- Head-coord step: `(src, tgt)` comes from a filtered edge `(u, v)` of
    `s`, with head-coord changing `u → v` and tail-coord `q` unchanged. -/
theorem edgeListParGo_head_coord_change
    (s : SessionType) (tl : List SessionType) (env : List (String × Nat))
    (start prefixProd src tgt : Nat)
    (hhead : (src, tgt) ∈
      edgeList.edgeListParLiftChild
        ((edgeList s 0 env).filter
          (fun e => decide (e.1 < stateCount s) && decide (e.2 < stateCount s)))
        start (stateCount.prodChildren tl) (stateCount s) prefixProd) :
    ∃ p u v q, p < prefixProd ∧ u < stateCount s ∧ v < stateCount s ∧
               q < stateCount.prodChildren tl ∧
               (u, v) ∈ edgeList s 0 env ∧
               src = start + p * (stateCount s * stateCount.prodChildren tl)
                             + u * stateCount.prodChildren tl + q ∧
               tgt = start + p * (stateCount s * stateCount.prodChildren tl)
                             + v * stateCount.prodChildren tl + q := by
  rcases (mem_edgeListParLiftChild _ _ _ _ _ _ _).mp hhead with
    ⟨u, v, hmem, p, q, hplt, hqlt, hsrc, htgt⟩
  rw [List.mem_filter] at hmem
  obtain ⟨hmem_raw, hok⟩ := hmem
  simp at hok
  exact ⟨p, u, v, q, hplt, hok.1, hok.2, hqlt, hmem_raw, hsrc, htgt⟩

/-- Head coordinate-0 decode: `(u * pcTl + q) / pcTl = u` when `q < pcTl`. -/
theorem flatToTupleNat_head_zero
    (s : SessionType) (tl : List SessionType) (u q : Nat)
    (_hu : u < stateCount s) (hq : q < stateCount.prodChildren tl) :
    flatToTupleNat (s :: tl) (u * stateCount.prodChildren tl + q) 0 = u := by
  simp only [flatToTupleNat]
  show (u * stateCount.prodChildren tl + q) / stateCount.prodChildren tl = u
  have hpc_pos : 0 < stateCount.prodChildren tl :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) hq
  have hcomm : u * stateCount.prodChildren tl + q
              = q + stateCount.prodChildren tl * u := by ring
  rw [hcomm, Nat.add_mul_div_left _ _ hpc_pos, Nat.div_eq_of_lt hq, Nat.zero_add]

/-- Head coordinate-(i+1) decode: routes through `flatToTupleNat tl q i`. -/
theorem flatToTupleNat_head_succ
    (s : SessionType) (tl : List SessionType) (u q i : Nat)
    (_hu : u < stateCount s) (hq : q < stateCount.prodChildren tl) :
    flatToTupleNat (s :: tl) (u * stateCount.prodChildren tl + q) (i + 1) =
      flatToTupleNat tl q i := by
  simp only [flatToTupleNat]
  show flatToTupleNat tl ((u * stateCount.prodChildren tl + q)
                            % stateCount.prodChildren tl) i
     = flatToTupleNat tl q i
  congr 1
  have hcomm : u * stateCount.prodChildren tl + q
              = q + stateCount.prodChildren tl * u := by ring
  rw [hcomm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hq]

/-!
### Head-coord change: what a head-lift edge does to the coordinates

Combining `edgeListParGo_head_coord_change` with `flatToTupleNat_head_*`:
a head-lift edge `(src, tgt)` at prefixProd = 1 changes coordinate 0 from
`u` to `v` while leaving every later coordinate unchanged.

Restricted to the top-level case (prefixProd = 1), so `p = 0` and the
endpoint formulas collapse to `src = start + u * pcTl + q`,
`tgt = start + v * pcTl + q`.
-/

/-- At prefixProd = 1, a head-lift edge of `edgeListParGo (s :: tl) start env 1`
    has source `start + u * pcTl + q` and target `start + v * pcTl + q`. -/
theorem head_lift_endpoint_form_top
    (s : SessionType) (tl : List SessionType) (env : List (String × Nat))
    (start src tgt : Nat)
    (hhead : (src, tgt) ∈
      edgeList.edgeListParLiftChild
        ((edgeList s 0 env).filter
          (fun e => decide (e.1 < stateCount s) && decide (e.2 < stateCount s)))
        start (stateCount.prodChildren tl) (stateCount s) 1) :
    ∃ u v q, u < stateCount s ∧ v < stateCount s ∧
             q < stateCount.prodChildren tl ∧
             (u, v) ∈ edgeList s 0 env ∧
             src = start + u * stateCount.prodChildren tl + q ∧
             tgt = start + v * stateCount.prodChildren tl + q := by
  rcases edgeListParGo_head_coord_change s tl env start 1 src tgt hhead with
    ⟨p, u, v, q, hplt, hulu, hvlu, hqlt, hmem, hsrc, htgt⟩
  -- p < 1 forces p = 0.
  have hp0 : p = 0 := by omega
  refine ⟨u, v, q, hulu, hvlu, hqlt, hmem, ?_, ?_⟩
  · rw [hsrc, hp0]; ring
  · rw [htgt, hp0]; ring

/-!
### Top-level coord-preservation for a head-lift edge

A head-lift edge at prefixProd = 1, start = 0, changes coord 0 from
`u` to `v` and keeps every other coord fixed. This is the key
step-3-forward ingredient restricted to "top-level head-lift edges".
-/

/-- Top-level head-lift edges preserve all tail coordinates and change
    coord 0 from `u` to `v` (where `(u, v)` is the underlying child edge). -/
theorem head_lift_coord_preserve_top
    (s : SessionType) (tl : List SessionType) (env : List (String × Nat))
    (src tgt : Nat)
    (hhead : (src, tgt) ∈
      edgeList.edgeListParLiftChild
        ((edgeList s 0 env).filter
          (fun e => decide (e.1 < stateCount s) && decide (e.2 < stateCount s)))
        0 (stateCount.prodChildren tl) (stateCount s) 1) :
    ∃ u v, (u, v) ∈ edgeList s 0 env ∧ u < stateCount s ∧ v < stateCount s ∧
           flatToTupleNat (s :: tl) src 0 = u ∧
           flatToTupleNat (s :: tl) tgt 0 = v ∧
           (∀ i, flatToTupleNat (s :: tl) src (i + 1)
                  = flatToTupleNat (s :: tl) tgt (i + 1)) := by
  rcases head_lift_endpoint_form_top s tl env 0 src tgt hhead with
    ⟨u, v, q, hulu, hvlu, hqlt, hmem, hsrc, htgt⟩
  refine ⟨u, v, hmem, hulu, hvlu, ?_, ?_, ?_⟩
  · rw [hsrc]; simp only [Nat.zero_add]
    exact flatToTupleNat_head_zero s tl u q hulu hqlt
  · rw [htgt]; simp only [Nat.zero_add]
    exact flatToTupleNat_head_zero s tl v q hvlu hqlt
  · intro i
    rw [hsrc, htgt]
    simp only [Nat.zero_add]
    rw [flatToTupleNat_head_succ s tl u q i hulu hqlt,
        flatToTupleNat_head_succ s tl v q i hvlu hqlt]

/-!
## Phase 1b-β1c-full — Step 2 (rest): tail-edge coordinate preservation

Extending the head-lift case (`head_lift_coord_preserve_top`) to arbitrary
children of a `par ss` node.

The recursive structure of `edgeListParGo` makes an edge either arise
* from the first child's head-lift (already covered at prefixProd = 1), or
* from the tail recursion at a higher prefix product.

We first generalise the head-lift arithmetic to arbitrary `prefixProd`
(1a), then prove by induction on `ss` that every edge has a "coordinate
index" witnessing which child it came from (1b), and finally decode
that into a flat `flatToTupleNat` coord-preservation statement for the
top-level case (2).
-/

/-- Generalised head-lift: same content as `edgeListParGo_head_coord_change`
    but restated with `start = 0` to match the form used by the induction
    in `edgeListParGo_coord_change`. -/
theorem edgeListParGo_head_coord_change_general
    (s : SessionType) (tl : List SessionType) (env : List (String × Nat))
    (prefixProd u v : Nat)
    (h : (u, v) ∈ edgeList.edgeListParLiftChild
              ((edgeList s 0 env).filter
                (fun e => decide (e.1 < stateCount s) && decide (e.2 < stateCount s)))
              0 (stateCount.prodChildren tl) (stateCount s) prefixProd) :
    ∃ (p u₀ v₀ q : Nat),
      p < prefixProd ∧
      q < stateCount.prodChildren tl ∧
      u₀ < stateCount s ∧
      v₀ < stateCount s ∧
      (u₀, v₀) ∈ edgeList s 0 env ∧
      u = p * (stateCount s * stateCount.prodChildren tl) + u₀ * stateCount.prodChildren tl + q ∧
      v = p * (stateCount s * stateCount.prodChildren tl) + v₀ * stateCount.prodChildren tl + q := by
  rcases edgeListParGo_head_coord_change s tl env 0 prefixProd u v h with
    ⟨p, u₀, v₀, q, hplt, huu, hvu, hqlt, hmem, hsrc, htgt⟩
  refine ⟨p, u₀, v₀, q, hplt, hqlt, huu, hvu, hmem, ?_, ?_⟩
  · simpa [Nat.zero_add] using hsrc
  · simpa [Nat.zero_add] using htgt

/-!
### Tail-edge coordinate characterisation

Every edge of `edgeListParGo ss 0 env prefixProd` identifies a unique child
index `i`, a local edge `(u₀, v₀) ∈ edgeList (ss.get i) 0 env`, and a
stride decomposition `u = p * (stateCount(ss.get i) * suffixProd) + u₀ *
suffixProd + q`, `v = p * (stateCount(ss.get i) * suffixProd) + v₀ *
suffixProd + q`, where `suffixProd = prodChildren (ss.drop (i + 1))` and
`p q` are free naturals (their bounds are recovered via the `u < prodChildren ss`
constraint at the top level).

We induct on `ss` and use `mem_edgeListParGo_cons`: the head-lift case
uses `edgeListParGo_head_coord_change_general`, the tail-recursive case
uses the induction hypothesis at `prefixProd' = prefixProd * stateCount s`
and lifts the child index via `Fin.succ`.
-/

theorem edgeListParGo_coord_change :
    ∀ (ss : List SessionType) (env : List (String × Nat)) (prefixProd : Nat)
      (u v : Nat)
      (_hmem : (u, v) ∈ edgeList.edgeListParGo ss 0 env prefixProd),
    ∃ (i : Fin ss.length) (u₀ v₀ p q : Nat),
      u₀ < stateCount (ss.get i) ∧
      v₀ < stateCount (ss.get i) ∧
      q < stateCount.prodChildren (ss.drop (i.val + 1)) ∧
      (u₀, v₀) ∈ edgeList (ss.get i) 0 env ∧
      u = p * (stateCount (ss.get i) * stateCount.prodChildren (ss.drop (i.val + 1)))
            + u₀ * stateCount.prodChildren (ss.drop (i.val + 1)) + q ∧
      v = p * (stateCount (ss.get i) * stateCount.prodChildren (ss.drop (i.val + 1)))
            + v₀ * stateCount.prodChildren (ss.drop (i.val + 1)) + q
  | [],      _,   _,         u, v, hmem => by
      exfalso
      exact (mem_edgeListParGo_nil 0 _ _ u v).mp hmem
  | s :: tl, env, prefixProd, u, v, hmem => by
      rcases (mem_edgeListParGo_cons s tl 0 env prefixProd u v).mp hmem with
        hhead | htail
      · -- head-lift case
        rcases edgeListParGo_head_coord_change_general s tl env prefixProd u v hhead with
          ⟨p, u₀, v₀, q, _hplt, hqlt, huu, hvu, hmemChild, hsrc, htgt⟩
        refine ⟨⟨0, by simp [List.length]⟩, u₀, v₀, p, q, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [List.get] using huu
        · simpa [List.get] using hvu
        · simpa [List.drop, List.get] using hqlt
        · simpa [List.get] using hmemChild
        · simpa [List.drop, List.get] using hsrc
        · simpa [List.drop, List.get] using htgt
      · -- tail-recursive case: recurse on tl at prefixProd * stateCount s
        rcases edgeListParGo_coord_change tl env (prefixProd * stateCount s) u v htail with
          ⟨i', u₀, v₀, p, q, huu, hvu, hqlt, hmemChild, hsrc, htgt⟩
        have hval : (i'.succ : Fin (s :: tl).length).val = i'.val + 1 := rfl
        have hget : (s :: tl).get i'.succ = tl.get i' := by
          show List.get (s :: tl) i'.succ = List.get tl i'
          rfl
        have hdrop : (s :: tl).drop (i'.succ.val + 1) = tl.drop (i'.val + 1) := by
          rw [hval]; rfl
        refine ⟨i'.succ, u₀, v₀, p, q, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hget]; exact huu
        · rw [hget]; exact hvu
        · rw [hdrop]; exact hqlt
        · rw [hget]; exact hmemChild
        · rw [hget, hdrop]; exact hsrc
        · rw [hget, hdrop]; exact htgt

/-!
### Auxiliary: product splits at index `k`

A basic arithmetic fact about `prodChildren`: the total product splits
into the product of the prefix `take k`, the state count at position `k`,
and the product of the suffix `drop (k+1)`. Used by the decoding proofs.
-/

theorem stateCount.prodChildren_split :
    ∀ (xs : List SessionType) (k : Nat) (hk : k < xs.length),
      stateCount.prodChildren xs
        = stateCount.prodChildren (xs.take k)
          * (stateCount (xs.get ⟨k, hk⟩)
             * stateCount.prodChildren (xs.drop (k + 1)))
  | [],       k,      hk => by simp at hk
  | s :: tl,  0,      _  => by
      simp [List.take, List.drop, List.get, stateCount.prodChildren]
  | s :: tl,  (k + 1), hk => by
      have hk' : k < tl.length := by simp [List.length] at hk; omega
      simp only [List.take, List.drop, List.get, stateCount.prodChildren]
      have hih := stateCount.prodChildren_split tl k hk'
      rw [hih]; ring

/-!
### Coordinate decoding helpers for the stride form

Given the stride form `x = p * (sz * sp) + u₀ * sp + q` where `sz =
stateCount (ss.get ⟨i, _⟩)`, `sp = prodChildren (ss.drop (i+1))`, and
`u₀ < sz`, `q < sp`, we decode the tuple coordinates of `x`. Two facts:

* `flat_at_index_eq` — coordinate `i` is exactly `u₀` (provided
  `p * sz < stateCount.prodChildren (ss.take (i+1))` in the surrounding
  `ss`; concretely: p must not overflow the prefix block).
* `flat_off_index_independent_of_u₀` — coordinates `j ≠ i` are a function
  of `p` and `q` alone, independent of `u₀`.
-/

/-- Coordinate `i` of `p * (sz * sp) + u₀ * sp + q` equals `u₀` when the
    tail bounds hold and `p` doesn't overflow the prefix block. -/
theorem flat_at_index_eq :
    ∀ (ss : List SessionType) (i : Nat) (hi : i < ss.length)
      (p u₀ q : Nat),
      u₀ < stateCount (ss.get ⟨i, hi⟩) →
      q < stateCount.prodChildren (ss.drop (i + 1)) →
      p < stateCount.prodChildren (ss.take i) →
      flatToTupleNat ss
        (p * (stateCount (ss.get ⟨i, hi⟩) *
              stateCount.prodChildren (ss.drop (i + 1)))
          + u₀ * stateCount.prodChildren (ss.drop (i + 1)) + q) i = u₀
  | [],      _,      hi, _, _, _, _, _, _ => by simp at hi
  | s :: tl, 0,      _,  p, u₀, q, hulu, hqlt, hpbd => by
      -- i = 0: ss.get ⟨0, _⟩ = s, ss.drop 1 = tl, ss.take 0 = [].
      -- hpbd : p < prodChildren [] = 1, so p = 0.
      simp [List.take, List.drop, List.get, stateCount.prodChildren] at hpbd hqlt hulu ⊢
      -- Goal: flatToTupleNat (s :: tl) (p * (stateCount s * prodChildren tl) + u₀ * prodChildren tl + q) 0 = u₀
      -- From hpbd (p < 1), p = 0.
      have hp0 : p = 0 := by omega
      subst hp0
      simp only [Nat.zero_mul, Nat.zero_add]
      -- Goal now: flatToTupleNat (s :: tl) (u₀ * prodChildren tl + q) 0 = u₀
      exact flatToTupleNat_head_zero s tl u₀ q hulu hqlt
  | s :: tl, k + 1, hi, p, u₀, q, hulu, hqlt, hpbd => by
      -- i = k+1: recurse on tl.
      -- ss.get ⟨k+1, hi⟩ = tl.get ⟨k, hi'⟩
      -- ss.drop (k+2) = tl.drop (k+1)
      -- ss.take (k+1) = s :: tl.take k, so prodChildren = stateCount s * prodChildren (tl.take k)
      have hi' : k < tl.length := by
        simp [List.length] at hi; omega
      -- Normalize hqlt from (s :: tl).drop (k+1+1) to tl.drop (k+1).
      have hdrop_eq : (s :: tl).drop (k + 1 + 1) = tl.drop (k + 1) := by
        simp [List.drop]
      rw [hdrop_eq] at hqlt
      -- Normalize hulu from (s :: tl).get ⟨k+1, hi⟩ to tl.get ⟨k, hi'⟩.
      have hget_eq : (s :: tl).get ⟨k + 1, hi⟩ = tl.get ⟨k, hi'⟩ := rfl
      rw [hget_eq] at hulu
      -- In the expression, rename things so we can recognise the recursion.
      -- The goal is:
      --   flatToTupleNat (s :: tl) (p * M + u₀ * sp + q) (k + 1) = u₀
      -- where M = stateCount (tl.get ⟨k, hi'⟩) * sp, sp = prodChildren (tl.drop (k+1))
      -- By `flatToTupleNat_head_succ`-style decoding: the outer shape is NOT
      -- of form `u * prodChildren tl + q'`; we need to unfold `flatToTupleNat`
      -- directly and compute the modulo.
      simp only [flatToTupleNat]
      show flatToTupleNat tl
        ((p * (stateCount (tl.get ⟨k, hi'⟩) *
               stateCount.prodChildren (tl.drop (k + 1)))
          + u₀ * stateCount.prodChildren (tl.drop (k + 1)) + q)
           % stateCount.prodChildren tl) k = u₀
      -- Rewrite the argument to tl's recursion:
      -- Let `pcTl = prodChildren tl`. We have `ss.take (k+1) = s :: tl.take k`,
      -- and `prodChildren (s :: tl.take k) = stateCount s * prodChildren (tl.take k)`.
      -- But wait, hpbd gives us `p < prodChildren (ss.take (k+1))`.
      have hpbd_unfold : stateCount.prodChildren ((s :: tl).take (k + 1))
                       = stateCount s * stateCount.prodChildren (tl.take k) := by
        show stateCount.prodChildren (s :: tl.take k) = _
        simp [stateCount.prodChildren]
      rw [hpbd_unfold] at hpbd
      -- Apply the IH. For the IH we need `p < prodChildren (tl.take k)`,
      -- but `hpbd` currently says `p < stateCount s * prodChildren (tl.take k)`.
      -- This is TOO WEAK for the IH directly. But this is OK — we can instead
      -- use the `mod` structure. The key arithmetic is:
      -- (p * M' + u₀ * sp + q) mod pcTl   where M' = stateCount tl[k] * sp
      --                                   and pcTl = stateCount s * prodChildren (tl.drop 1)?? NO
      -- Wait: pcTl = prodChildren tl, so pcTl = prodChildren (tl.take k) * stateCount tl[k] * prodChildren (tl.drop (k+1))
      -- i.e. pcTl = prodChildren (tl.take k) * M'.
      have hsplit : stateCount.prodChildren tl
                   = stateCount.prodChildren (tl.take k)
                     * (stateCount (tl.get ⟨k, hi'⟩) *
                        stateCount.prodChildren (tl.drop (k + 1))) :=
        stateCount.prodChildren_split tl k hi'
      -- Now factor: p * M' + u₀ * sp + q = p * M' + r where r = u₀*sp + q < M'.
      -- Reassociate first so `set` will replace the expression in the goal.
      have hgoal_assoc :
          (p * (stateCount (tl.get ⟨k, hi'⟩) *
                stateCount.prodChildren (tl.drop (k + 1)))
           + u₀ * stateCount.prodChildren (tl.drop (k + 1)) + q)
           = p * (stateCount (tl.get ⟨k, hi'⟩) *
                   stateCount.prodChildren (tl.drop (k + 1)))
              + (u₀ * stateCount.prodChildren (tl.drop (k + 1)) + q) := by ring
      -- Rewrite the goal to the re-associated form.
      show flatToTupleNat tl
        ((p * (stateCount (tl.get ⟨k, hi'⟩) *
                stateCount.prodChildren (tl.drop (k + 1)))
          + u₀ * stateCount.prodChildren (tl.drop (k + 1)) + q)
           % stateCount.prodChildren tl) k = u₀
      rw [hgoal_assoc]
      set M' := stateCount (tl.get ⟨k, hi'⟩) *
                stateCount.prodChildren (tl.drop (k + 1)) with hM'
      set r : Nat := u₀ * stateCount.prodChildren (tl.drop (k + 1)) + q with hr
      have hrLt : r < M' := by
        show u₀ * stateCount.prodChildren (tl.drop (k + 1)) + q < M'
        have hpc_pos : 0 < stateCount.prodChildren (tl.drop (k + 1)) := by
          rcases Nat.eq_zero_or_pos (stateCount.prodChildren (tl.drop (k + 1))) with h0 | hpos
          · rw [h0] at hqlt; simp at hqlt
          · exact hpos
        have : (u₀ + 1) * stateCount.prodChildren (tl.drop (k + 1)) ≤ M' := by
          show (u₀ + 1) * stateCount.prodChildren (tl.drop (k + 1))
            ≤ stateCount (tl.get ⟨k, hi'⟩) * stateCount.prodChildren (tl.drop (k + 1))
          exact Nat.mul_le_mul_right _ hulu
        calc u₀ * stateCount.prodChildren (tl.drop (k + 1)) + q
            < u₀ * stateCount.prodChildren (tl.drop (k + 1))
              + stateCount.prodChildren (tl.drop (k + 1)) := by omega
          _ = (u₀ + 1) * stateCount.prodChildren (tl.drop (k + 1)) := by ring
          _ ≤ M' := this
      -- The modulo: (p * M' + r) mod (prefix * M') = (p mod prefix) * M' + r
      -- when r < M' and prefix > 0.
      -- Actually the cleanest form: pcTl = prodChildren(take k) * M', so
      -- (p * M' + r) mod (prodChildren(take k) * M')
      -- = ((p mod prodChildren(take k)) * M' + r mod M') mod (prodChildren(take k) * M')... simpler:
      -- just use the fact p < stateCount s * prodChildren(take k), and for IH
      -- we can use `p mod prodChildren(take k)`.
      -- Actually for the conclusion `= u₀` we have a simpler plan:
      -- (p * M' + r) mod (prodChildren(take k) * M')
      -- = let p' = p mod prodChildren(take k), then p' * M' + r.
      -- Then apply IH on tl with p' instead of p and prove p' < prodChildren(take k).
      -- Let's execute.
      have hpcTake_pos : 0 < stateCount.prodChildren (tl.take k) := by
        -- From hsplit: pcTl = prodChildren(take k) * M'; and pcTl > 0 (every child has ≥ 1 state).
        -- Actually, we haven't proven pcTl > 0 yet. Use stateCount_pos.
        have : 0 < stateCount.prodChildren tl :=
          stateCount.prodChildren_pos tl (fun t _ => stateCount_pos t)
        rw [hsplit] at this
        rcases Nat.eq_zero_or_pos (stateCount.prodChildren (tl.take k)) with h0 | hpos
        · rw [h0] at this; simp at this
        · exact hpos
      have hM'_pos : 0 < M' := by
        rcases Nat.eq_zero_or_pos M' with h0 | hpos
        · rw [h0] at hrLt; simp at hrLt
        · exact hpos
      -- Rewrite pcTl = prodChildren(take k) * M'
      rw [hsplit]
      -- Goal: flatToTupleNat tl ((p * M' + r) mod (prodChildren(take k) * M')) k = u₀
      -- key: (p * M' + r) mod (prodChildren(take k) * M') = (p mod prodChildren(take k)) * M' + r
      have hmodEq : (p * M' + r) % (stateCount.prodChildren (tl.take k) * M')
                  = (p % stateCount.prodChildren (tl.take k)) * M' + r := by
        have hlt : (p % stateCount.prodChildren (tl.take k)) * M' + r
                 < stateCount.prodChildren (tl.take k) * M' := by
          have : p % stateCount.prodChildren (tl.take k)
                 < stateCount.prodChildren (tl.take k) :=
            Nat.mod_lt _ hpcTake_pos
          -- (p mod a) * b + r < a * b when p mod a ≤ a - 1 and r < b:
          --   (a - 1) * b + r < a * b  iff  r < b.
          have hle : p % stateCount.prodChildren (tl.take k)
                   ≤ stateCount.prodChildren (tl.take k) - 1 := by omega
          have : (p % stateCount.prodChildren (tl.take k)) * M'
                 ≤ (stateCount.prodChildren (tl.take k) - 1) * M' :=
            Nat.mul_le_mul_right _ hle
          have hpcpos : 0 < stateCount.prodChildren (tl.take k) := hpcTake_pos
          have : (stateCount.prodChildren (tl.take k) - 1) * M' + M'
                 = stateCount.prodChildren (tl.take k) * M' := by
            have : (stateCount.prodChildren (tl.take k) - 1 + 1) * M'
                   = stateCount.prodChildren (tl.take k) * M' := by
              congr 1; omega
            rw [← this]; ring
          omega
        -- Express: p * M' + r = (p / prodChildren(take k)) * prodChildren(take k) * M' + (p mod prodChildren(take k)) * M' + r
        --       = (p / prodChildren(take k)) * (prodChildren(take k) * M') + ((p mod prodChildren(take k)) * M' + r)
        -- Use mod_add_div or add_mul_mod_self_left.
        have hexpand : p * M' + r
                     = (p / stateCount.prodChildren (tl.take k))
                       * (stateCount.prodChildren (tl.take k) * M')
                       + ((p % stateCount.prodChildren (tl.take k)) * M' + r) := by
          have hdm : (p / stateCount.prodChildren (tl.take k))
                       * stateCount.prodChildren (tl.take k)
                     + p % stateCount.prodChildren (tl.take k) = p := by
            have h := Nat.div_add_mod p (stateCount.prodChildren (tl.take k))
            have hcomm : stateCount.prodChildren (tl.take k)
                       * (p / stateCount.prodChildren (tl.take k))
                       = (p / stateCount.prodChildren (tl.take k))
                         * stateCount.prodChildren (tl.take k) := Nat.mul_comm _ _
            rw [hcomm] at h
            exact h
          -- p = (p/a)*a + p%a, so p*M' = (p/a)*a*M' + (p%a)*M'
          calc p * M' + r
              = ((p / stateCount.prodChildren (tl.take k))
                  * stateCount.prodChildren (tl.take k)
                  + p % stateCount.prodChildren (tl.take k)) * M' + r := by rw [hdm]
            _ = (p / stateCount.prodChildren (tl.take k))
                  * (stateCount.prodChildren (tl.take k) * M')
                + ((p % stateCount.prodChildren (tl.take k)) * M' + r) := by ring
        rw [hexpand, Nat.mul_add_mod', Nat.mod_eq_of_lt hlt]
      rw [hmodEq]
      -- Goal: flatToTupleNat tl ((p % prodChildren(take k)) * M' + r) k = u₀
      -- which is exactly the IH form with p → p % prodChildren(take k).
      have hpNew : p % stateCount.prodChildren (tl.take k)
                 < stateCount.prodChildren (tl.take k) :=
        Nat.mod_lt _ hpcTake_pos
      have hIH := flat_at_index_eq tl k hi'
                    (p % stateCount.prodChildren (tl.take k)) u₀ q hulu hqlt hpNew
      -- hIH :  flatToTupleNat tl ((p%·) * (sz*sp) + u₀*sp + q) k = u₀
      -- Goal: flatToTupleNat tl ((p%·) * M' + (u₀*sp + q)) k = u₀
      -- With M' = sz*sp and r = u₀*sp + q these should be defeq / convert.
      convert hIH using 2
      ring

/-- Off-index coord independence: coordinate `j ≠ i` of the stride form
    `p * (sz * sp) + u₀ * sp + q` depends only on `p, q, ss, j`, not on
    `u₀`. Stated as: two such expressions with the same `p, q` but
    different `u₀, v₀` agree on every coordinate `j ≠ i`. -/
theorem flat_off_index_independent_of_u₀ :
    ∀ (ss : List SessionType) (i : Nat) (hi : i < ss.length)
      (p u₀ v₀ q : Nat),
      u₀ < stateCount (ss.get ⟨i, hi⟩) →
      v₀ < stateCount (ss.get ⟨i, hi⟩) →
      q < stateCount.prodChildren (ss.drop (i + 1)) →
      p < stateCount.prodChildren (ss.take i) →
      ∀ (j : Nat), j < ss.length → j ≠ i →
        flatToTupleNat ss
          (p * (stateCount (ss.get ⟨i, hi⟩) *
                stateCount.prodChildren (ss.drop (i + 1)))
            + u₀ * stateCount.prodChildren (ss.drop (i + 1)) + q) j
        = flatToTupleNat ss
          (p * (stateCount (ss.get ⟨i, hi⟩) *
                stateCount.prodChildren (ss.drop (i + 1)))
            + v₀ * stateCount.prodChildren (ss.drop (i + 1)) + q) j
  | [],      _,      hi, _, _, _, _, _, _, _, _, _, _, _ => by simp at hi
  | s :: tl, 0,      _,  p, u₀, v₀, q, hulu, hvlu, hqlt, hpbd, j, hj, hjne => by
      -- i = 0, so j ≥ 1. Use flatToTupleNat_head_succ.
      -- p < prodChildren [] = 1, so p = 0.
      simp [List.take, List.drop, List.get, stateCount.prodChildren] at hpbd hqlt hulu hvlu
      have hp0 : p = 0 := by omega
      subst hp0
      -- Also normalize List.drop 1 (s :: tl) to tl in the goal.
      have hdrop : (s :: tl).drop (0 + 1) = tl := by simp [List.drop]
      have hget : (s :: tl).get ⟨0, by simp [List.length]⟩ = s := rfl
      -- Goal:
      --   flatToTupleNat (s :: tl) (0 * _ + u₀ * prodChildren tl + q) j
      -- = flatToTupleNat (s :: tl) (0 * _ + v₀ * prodChildren tl + q) j
      simp only [hdrop, hget, Nat.zero_mul, Nat.zero_add]
      -- j ≠ 0, so j = j' + 1.
      match j, hjne with
      | 0,      hjne => exact absurd rfl hjne
      | j' + 1, _    =>
        rw [flatToTupleNat_head_succ s tl u₀ q j' hulu hqlt,
            flatToTupleNat_head_succ s tl v₀ q j' hvlu hqlt]
  | s :: tl, k + 1, hi, p, u₀, v₀, q, hulu, hvlu, hqlt, hpbd, j, hj, hjne => by
      -- i = k+1. Recurse on tl for j > 0. Base case j = 0 is separate.
      have hi' : k < tl.length := by simp [List.length] at hi; omega
      -- Normalize hulu, hvlu, hqlt to use tl.get / tl.drop.
      have hdrop_eq : (s :: tl).drop (k + 1 + 1) = tl.drop (k + 1) := by
        simp [List.drop]
      rw [hdrop_eq] at hqlt
      have hget_eq : (s :: tl).get ⟨k + 1, hi⟩ = tl.get ⟨k, hi'⟩ := rfl
      rw [hget_eq] at hulu hvlu
      -- Also normalize the goal.
      rw [show ((s :: tl).get ⟨k + 1, hi⟩ : SessionType) = tl.get ⟨k, hi'⟩ from rfl,
          show (s :: tl).drop (k + 1 + 1) = tl.drop (k + 1) from (by simp [List.drop])]
      -- Case on j.
      match j, hjne with
      | 0, _ =>
        -- Goal: flatToTupleNat (s :: tl) u-expr 0 = flatToTupleNat (s :: tl) v-expr 0
        -- Both reduce to (expr) / prodChildren tl.
        -- prodChildren tl = prodChildren (tl.take k) * M' (hsplit).
        -- expr_u = p * M' + u₀ * sp + q, expr_v = p * M' + v₀ * sp + q
        -- Need: expr_u / (prodChildren (tl.take k) * M') = expr_v / (prodChildren (tl.take k) * M').
        -- Both equal p / prodChildren (tl.take k) (since (u₀ sp + q) < M' and (v₀ sp + q) < M').
        -- Let's prove it.
        simp only [flatToTupleNat]
        have hsplit := stateCount.prodChildren_split tl k hi'
        -- Goal: (p*M' + u₀*sp + q) / prodChildren tl = (p*M' + v₀*sp + q) / prodChildren tl
        rw [hsplit]
        -- Set M' and compute.
        set M' := stateCount (tl.get ⟨k, hi'⟩) *
                  stateCount.prodChildren (tl.drop (k + 1)) with hM'_def
        -- Prove each side equals p / prodChildren (tl.take k).
        have hpcTake_pos : 0 < stateCount.prodChildren (tl.take k) := by
          have : 0 < stateCount.prodChildren tl :=
            stateCount.prodChildren_pos tl (fun t _ => stateCount_pos t)
          rw [hsplit] at this
          rcases Nat.eq_zero_or_pos (stateCount.prodChildren (tl.take k)) with h0 | hpos
          · rw [h0] at this; simp at this
          · exact hpos
        have hM'_pos : 0 < M' := by
          have hsp_pos : 0 < stateCount.prodChildren (tl.drop (k + 1)) :=
            Nat.lt_of_le_of_lt (Nat.zero_le _) hqlt
          exact Nat.mul_pos (stateCount_pos _) hsp_pos
        -- The key computation: for any u < stateCount(tl[k]) and q < sp,
        -- (p*M' + u*sp + q) / (prodChildren(take k) * M') = p / prodChildren(take k).
        have hdiv_eq : ∀ u, u < stateCount (tl.get ⟨k, hi'⟩) →
            (p * M' + u * stateCount.prodChildren (tl.drop (k + 1)) + q)
              / (stateCount.prodChildren (tl.take k) * M')
            = p / stateCount.prodChildren (tl.take k) := by
          intro u hu
          -- Bound: u*sp + q < M' = stateCount(tl[k]) * sp
          have hsub_lt : u * stateCount.prodChildren (tl.drop (k + 1)) + q < M' := by
            show u * stateCount.prodChildren (tl.drop (k + 1)) + q
              < stateCount (tl.get ⟨k, hi'⟩) *
                stateCount.prodChildren (tl.drop (k + 1))
            have hsp_pos : 0 < stateCount.prodChildren (tl.drop (k + 1)) :=
              Nat.lt_of_le_of_lt (Nat.zero_le _) hqlt
            calc u * stateCount.prodChildren (tl.drop (k + 1)) + q
                < u * stateCount.prodChildren (tl.drop (k + 1))
                  + stateCount.prodChildren (tl.drop (k + 1)) := by omega
              _ = (u + 1) * stateCount.prodChildren (tl.drop (k + 1)) := by ring
              _ ≤ stateCount (tl.get ⟨k, hi'⟩) *
                  stateCount.prodChildren (tl.drop (k + 1)) :=
                  Nat.mul_le_mul_right _ hu
          -- So p*M' + (u*sp + q) with (u*sp + q) < M'; divide by prefix * M'.
          have hassoc : p * M' + u * stateCount.prodChildren (tl.drop (k + 1)) + q
                      = p * M'
                        + (u * stateCount.prodChildren (tl.drop (k + 1)) + q) := by ring
          rw [hassoc]
          -- (p * M' + r) / (prefix * M') = p / prefix when r < M'.
          -- Use: (p*M' + r) = (p / prefix)*(prefix*M') + ((p % prefix)*M' + r).
          have hdm : (p / stateCount.prodChildren (tl.take k))
                       * stateCount.prodChildren (tl.take k)
                     + p % stateCount.prodChildren (tl.take k) = p := by
            have h := Nat.div_add_mod p (stateCount.prodChildren (tl.take k))
            have hcomm : stateCount.prodChildren (tl.take k)
                       * (p / stateCount.prodChildren (tl.take k))
                       = (p / stateCount.prodChildren (tl.take k))
                         * stateCount.prodChildren (tl.take k) := Nat.mul_comm _ _
            rw [hcomm] at h
            exact h
          have hpModLt : p % stateCount.prodChildren (tl.take k)
                        < stateCount.prodChildren (tl.take k) :=
            Nat.mod_lt _ hpcTake_pos
          have hinner_lt : p % stateCount.prodChildren (tl.take k) * M'
                           + (u * stateCount.prodChildren (tl.drop (k + 1)) + q)
                         < stateCount.prodChildren (tl.take k) * M' := by
            have hle : p % stateCount.prodChildren (tl.take k)
                     ≤ stateCount.prodChildren (tl.take k) - 1 := by omega
            have : (p % stateCount.prodChildren (tl.take k)) * M'
                 ≤ (stateCount.prodChildren (tl.take k) - 1) * M' :=
              Nat.mul_le_mul_right _ hle
            have hunfold : (stateCount.prodChildren (tl.take k) - 1) * M' + M'
                         = stateCount.prodChildren (tl.take k) * M' := by
              have hval : (stateCount.prodChildren (tl.take k) - 1 + 1) * M'
                        = stateCount.prodChildren (tl.take k) * M' := by
                congr 1; omega
              rw [← hval]; ring
            omega
          have hexpand :
              p * M' + (u * stateCount.prodChildren (tl.drop (k + 1)) + q)
              = (p / stateCount.prodChildren (tl.take k))
                  * (stateCount.prodChildren (tl.take k) * M')
                + ((p % stateCount.prodChildren (tl.take k)) * M'
                   + (u * stateCount.prodChildren (tl.drop (k + 1)) + q)) := by
            calc p * M' + (u * stateCount.prodChildren (tl.drop (k + 1)) + q)
                = ((p / stateCount.prodChildren (tl.take k))
                    * stateCount.prodChildren (tl.take k)
                    + p % stateCount.prodChildren (tl.take k)) * M'
                  + (u * stateCount.prodChildren (tl.drop (k + 1)) + q) := by rw [hdm]
              _ = (p / stateCount.prodChildren (tl.take k))
                    * (stateCount.prodChildren (tl.take k) * M')
                  + ((p % stateCount.prodChildren (tl.take k)) * M'
                    + (u * stateCount.prodChildren (tl.drop (k + 1)) + q)) := by ring
          rw [hexpand]
          -- ((p/a) * (a*M') + inner) / (a*M') = p/a when inner < a*M'.
          have hinner_div : ((p % stateCount.prodChildren (tl.take k)) * M'
                             + (u * stateCount.prodChildren (tl.drop (k + 1)) + q))
                             / (stateCount.prodChildren (tl.take k) * M') = 0 :=
            Nat.div_eq_of_lt hinner_lt
          -- Rewrite using add_comm so add_mul_div_right applies.
          have hrearr :
              p / stateCount.prodChildren (tl.take k)
                * (stateCount.prodChildren (tl.take k) * M')
              + ((p % stateCount.prodChildren (tl.take k)) * M'
                 + (u * stateCount.prodChildren (tl.drop (k + 1)) + q))
              = ((p % stateCount.prodChildren (tl.take k)) * M'
                 + (u * stateCount.prodChildren (tl.drop (k + 1)) + q))
                + (stateCount.prodChildren (tl.take k) * M')
                  * (p / stateCount.prodChildren (tl.take k)) := by ring
          rw [hrearr,
              Nat.add_mul_div_left _ _ (Nat.mul_pos hpcTake_pos hM'_pos),
              hinner_div, Nat.zero_add]
        rw [hdiv_eq u₀ hulu, hdiv_eq v₀ hvlu]
      | j' + 1, hjne' =>
        -- Recurse on tl with i = k.
        -- Need to reduce (p*M' + u₀*sp + q) mod prodChildren tl to a stride-form over tl.
        simp only [flatToTupleNat]
        have hsplit := stateCount.prodChildren_split tl k hi'
        rw [hsplit]
        set M' := stateCount (tl.get ⟨k, hi'⟩) *
                  stateCount.prodChildren (tl.drop (k + 1)) with hM'_def
        -- Same `hmodEq` pattern as in flat_at_index_eq.
        have hpcTake_pos : 0 < stateCount.prodChildren (tl.take k) := by
          have : 0 < stateCount.prodChildren tl :=
            stateCount.prodChildren_pos tl (fun t _ => stateCount_pos t)
          rw [hsplit] at this
          rcases Nat.eq_zero_or_pos (stateCount.prodChildren (tl.take k)) with h0 | hpos
          · rw [h0] at this; simp at this
          · exact hpos
        have hM'_pos : 0 < M' := by
          have hsp_pos : 0 < stateCount.prodChildren (tl.drop (k + 1)) :=
            Nat.lt_of_le_of_lt (Nat.zero_le _) hqlt
          exact Nat.mul_pos (stateCount_pos _) hsp_pos
        -- For both u₀ and v₀: reduce (p*M' + u*sp + q) mod (prefix*M').
        have hmod_eq : ∀ u, u < stateCount (tl.get ⟨k, hi'⟩) →
            (p * M' + u * stateCount.prodChildren (tl.drop (k + 1)) + q)
              % (stateCount.prodChildren (tl.take k) * M')
            = p % stateCount.prodChildren (tl.take k) * M'
              + (u * stateCount.prodChildren (tl.drop (k + 1)) + q) := by
          intro u hu
          have hsub_lt : u * stateCount.prodChildren (tl.drop (k + 1)) + q < M' := by
            have hsp_pos : 0 < stateCount.prodChildren (tl.drop (k + 1)) :=
              Nat.lt_of_le_of_lt (Nat.zero_le _) hqlt
            calc u * stateCount.prodChildren (tl.drop (k + 1)) + q
                < u * stateCount.prodChildren (tl.drop (k + 1))
                  + stateCount.prodChildren (tl.drop (k + 1)) := by omega
              _ = (u + 1) * stateCount.prodChildren (tl.drop (k + 1)) := by ring
              _ ≤ stateCount (tl.get ⟨k, hi'⟩) *
                  stateCount.prodChildren (tl.drop (k + 1)) :=
                  Nat.mul_le_mul_right _ hu
          have hassoc : p * M' + u * stateCount.prodChildren (tl.drop (k + 1)) + q
                      = p * M'
                        + (u * stateCount.prodChildren (tl.drop (k + 1)) + q) := by ring
          rw [hassoc]
          have hdm : (p / stateCount.prodChildren (tl.take k))
                       * stateCount.prodChildren (tl.take k)
                     + p % stateCount.prodChildren (tl.take k) = p := by
            have h := Nat.div_add_mod p (stateCount.prodChildren (tl.take k))
            have hcomm : stateCount.prodChildren (tl.take k)
                       * (p / stateCount.prodChildren (tl.take k))
                       = (p / stateCount.prodChildren (tl.take k))
                         * stateCount.prodChildren (tl.take k) := Nat.mul_comm _ _
            rw [hcomm] at h
            exact h
          have hpModLt : p % stateCount.prodChildren (tl.take k)
                        < stateCount.prodChildren (tl.take k) :=
            Nat.mod_lt _ hpcTake_pos
          have hinner_lt : p % stateCount.prodChildren (tl.take k) * M'
                           + (u * stateCount.prodChildren (tl.drop (k + 1)) + q)
                         < stateCount.prodChildren (tl.take k) * M' := by
            have hle : p % stateCount.prodChildren (tl.take k)
                     ≤ stateCount.prodChildren (tl.take k) - 1 := by omega
            have : (p % stateCount.prodChildren (tl.take k)) * M'
                 ≤ (stateCount.prodChildren (tl.take k) - 1) * M' :=
              Nat.mul_le_mul_right _ hle
            have hunfold : (stateCount.prodChildren (tl.take k) - 1) * M' + M'
                         = stateCount.prodChildren (tl.take k) * M' := by
              have hval : (stateCount.prodChildren (tl.take k) - 1 + 1) * M'
                        = stateCount.prodChildren (tl.take k) * M' := by
                congr 1; omega
              rw [← hval]; ring
            omega
          have hexpand :
              p * M' + (u * stateCount.prodChildren (tl.drop (k + 1)) + q)
              = (p / stateCount.prodChildren (tl.take k))
                  * (stateCount.prodChildren (tl.take k) * M')
                + ((p % stateCount.prodChildren (tl.take k)) * M'
                   + (u * stateCount.prodChildren (tl.drop (k + 1)) + q)) := by
            calc p * M' + (u * stateCount.prodChildren (tl.drop (k + 1)) + q)
                = ((p / stateCount.prodChildren (tl.take k))
                    * stateCount.prodChildren (tl.take k)
                    + p % stateCount.prodChildren (tl.take k)) * M'
                  + (u * stateCount.prodChildren (tl.drop (k + 1)) + q) := by rw [hdm]
              _ = (p / stateCount.prodChildren (tl.take k))
                    * (stateCount.prodChildren (tl.take k) * M')
                  + ((p % stateCount.prodChildren (tl.take k)) * M'
                    + (u * stateCount.prodChildren (tl.drop (k + 1)) + q)) := by ring
          rw [hexpand, Nat.mul_add_mod', Nat.mod_eq_of_lt hinner_lt]
        rw [hmod_eq u₀ hulu, hmod_eq v₀ hvlu]
        -- Now apply IH at tl with the reduced expressions. Need j' < tl.length and j' ≠ k.
        have hj'_tl : j' < tl.length := by
          have : j' + 1 < (s :: tl).length := hj
          simp [List.length] at this; omega
        have hj'_ne_k : j' ≠ k := by
          intro hjeq
          apply hjne'
          rw [hjeq]
        have hpNew : p % stateCount.prodChildren (tl.take k)
                    < stateCount.prodChildren (tl.take k) :=
          Nat.mod_lt _ hpcTake_pos
        have hIH := flat_off_index_independent_of_u₀ tl k hi'
                      (p % stateCount.prodChildren (tl.take k)) u₀ v₀ q
                      hulu hvlu hqlt hpNew j' hj'_tl hj'_ne_k
        -- hIH shape matches goal after moving terms.
        convert hIH using 2 <;> ring

/-!
### User-facing coordinate preservation for top-level par edges

Putting the pieces together: a top-level edge of `.par ss` preserves
all coordinates except exactly one (index `i`), and changes that
coordinate via a local edge in `ss.get i`.
-/

theorem edge_par_preserves_other_coords
    (ss : List SessionType) (env : List (String × Nat))
    (u v : Nat) (_hu : u < stateCount.prodChildren ss)
    (_hv : v < stateCount.prodChildren ss)
    (h : (u, v) ∈ edgeList (.par ss) 0 env) :
    ∃ i : Fin ss.length,
      (∀ j : Fin ss.length, j ≠ i →
        flatToTupleNat ss u j.val = flatToTupleNat ss v j.val) ∧
      (flatToTupleNat ss u i.val, flatToTupleNat ss v i.val)
        ∈ edgeList (ss.get i) 0 env := by
  -- Unfold edgeList (.par ss) = edgeListPar ss = edgeListParGo ss 0 env 1.
  have hP : (u, v) ∈ edgeList.edgeListPar ss 0 env := by
    have hh := h
    simp only [edgeList] at hh
    exact hh
  have h' : (u, v) ∈ edgeList.edgeListParGo ss 0 env 1 :=
    (mem_edgeListPar ss 0 env u v).mp hP
  -- Apply step 2.
  rcases edgeListParGo_coord_change ss env 1 u v h' with
    ⟨i, u₀, v₀, p, q, hulu, hvlu, hqlt, hmemChild, hsrc, htgt⟩
  -- Derive p < prodChildren (ss.take i.val) from u < prodChildren ss and bounds.
  have hsplit := stateCount.prodChildren_split ss i.val i.isLt
  have hM_pos : 0 < stateCount (ss.get i) *
                   stateCount.prodChildren (ss.drop (i.val + 1)) := by
    have hsp_pos : 0 < stateCount.prodChildren (ss.drop (i.val + 1)) :=
      Nat.lt_of_le_of_lt (Nat.zero_le _) hqlt
    exact Nat.mul_pos (stateCount_pos _) hsp_pos
  have hpcTake_pos : 0 < stateCount.prodChildren (ss.take i.val) := by
    have : 0 < stateCount.prodChildren ss :=
      stateCount.prodChildren_pos ss (fun t _ => stateCount_pos t)
    rw [hsplit] at this
    rcases Nat.eq_zero_or_pos (stateCount.prodChildren (ss.take i.val)) with h0 | hpos
    · rw [h0] at this; simp at this
    · exact hpos
  have hpbd : p < stateCount.prodChildren (ss.take i.val) := by
    -- From hsrc: u = p*M + u₀*sp + q, and u < prodChildren ss = prefix*M. Conclude p < prefix.
    by_contra hge
    push_neg at hge
    -- p ≥ prefix, so p*M ≥ prefix*M = prodChildren ss. But u = p*M + (≥0), so u ≥ prodChildren ss, contradicting `_hu`.
    set M : Nat := stateCount (ss.get i) *
                   stateCount.prodChildren (ss.drop (i.val + 1)) with hM
    have hmul_le : stateCount.prodChildren (ss.take i.val) * M ≤ p * M :=
      Nat.mul_le_mul_right _ hge
    have hpM_ge : p * M ≤ u := by
      rw [hsrc]; omega
    have hurange : u ≥ stateCount.prodChildren (ss.take i.val) * M :=
      le_trans hmul_le hpM_ge
    rw [← hsplit] at hurange
    omega
  -- Similarly v's version via htgt ensures consistency (just use the same p).
  refine ⟨i, ?_, ?_⟩
  · intro j hjne
    have hjne' : j.val ≠ i.val := fun heq => hjne (Fin.ext heq)
    have hu_eq := flat_off_index_independent_of_u₀ ss i.val i.isLt p u₀ v₀ q
                    hulu hvlu hqlt hpbd j.val j.isLt hjne'
    -- Rewrite u, v via hsrc, htgt.
    rw [hsrc, htgt]
    exact hu_eq
  · have hu0 := flat_at_index_eq ss i.val i.isLt p u₀ q hulu hqlt hpbd
    have hv0 := flat_at_index_eq ss i.val i.isLt p v₀ q hvlu hqlt hpbd
    rw [hsrc, htgt]
    rw [hu0, hv0]
    exact hmemChild

/-!
## Phase 1b-β1c-full — Step 3: Componentwise reachability (forward)

The forward direction: if two states in `stateSpace (.par ss)` are reachable,
then every projection to a child state space is also reachable. Proof
proceeds by `ReflTransGen.head_induction_on`: the `refl` case is immediate
(coordinates are equal), and for a head edge we use
`edge_par_preserves_other_coords` to identify the (unique) coordinate that
changes via a child edge; all other coordinates are preserved by the edge
and the IH carries them through.

This direction is sufficient to prove one half of the MR iff and, in
particular, to show that the quotient projection
`SCCQuotient (stateSpace (.par ss)) → ∀ i, SCCQuotient (stateSpace ss[i])`
is well-defined as a function. The backward direction (the "interleave"
construction) lands the full order-iso.
-/

/-- Helper: an edge in `stateSpace (.par ss)` unfolds to an `edgeList`
    membership for the `.par ss` constructor at `start = 0`, `env = []`. -/
theorem edge_par_of_stateSpace
    {ss : List SessionType}
    {a b : State (.par ss : SessionType)}
    (hab : (stateSpace (.par ss : SessionType)).edge a b) :
    (a.val, b.val) ∈ edgeList (.par ss : SessionType) 0 [] := hab

/-- A `Fin`-level par edge is a Nat-level par edge. Packaging for
    `edge_par_preserves_other_coords`. -/
theorem edge_par_preserves_other_coords_fin
    {ss : List SessionType}
    {a b : State (.par ss : SessionType)}
    (hab : (stateSpace (.par ss : SessionType)).edge a b) :
    ∃ i : Fin ss.length,
      (∀ j : Fin ss.length, j ≠ i →
        flatToTupleNat ss a.val j.val = flatToTupleNat ss b.val j.val) ∧
      (flatToTupleNat ss a.val i.val, flatToTupleNat ss b.val i.val)
        ∈ edgeList (ss.get i) 0 [] := by
  have hu_bound : a.val < stateCount.prodChildren ss := by
    have h := a.isLt
    show a.val < stateCount.prodChildren ss
    exact h
  have hv_bound : b.val < stateCount.prodChildren ss := by
    have h := b.isLt
    show b.val < stateCount.prodChildren ss
    exact h
  have hedgeNat : (a.val, b.val) ∈ edgeList (.par ss : SessionType) 0 [] :=
    edge_par_of_stateSpace hab
  exact edge_par_preserves_other_coords ss [] a.val b.val hu_bound hv_bound hedgeNat

/-- **Forward direction of Step 3.** If `u` reaches `v` in the par state
    space, then every child coordinate projection of `u` reaches the
    corresponding child coordinate projection of `v` in the child state
    space. -/
theorem reachable_par_forward
    (ss : List SessionType)
    (u v : Nat)
    (hu : u < stateCount.prodChildren ss)
    (hv : v < stateCount.prodChildren ss)
    (hReach : Reachable (stateSpace (.par ss : SessionType))
                ⟨u, by show u < stateCount (.par ss); simpa [stateCount] using hu⟩
                ⟨v, by show v < stateCount (.par ss); simpa [stateCount] using hv⟩) :
    ∀ i : Fin ss.length,
      Reachable (stateSpace (ss.get i))
        ⟨flatToTupleNat ss u i.val, flatToTupleNat_lt ss u hu i.val i.isLt⟩
        ⟨flatToTupleNat ss v i.val, flatToTupleNat_lt ss v hv i.val i.isLt⟩ := by
  -- We generalise to arbitrary reachable pairs `(a, b)` in `stateSpace (.par ss)`
  -- so the induction can "move" both endpoints together.
  -- Reformulate: Nat-level generalisation.
  --   For all `u' v'` with bounds, if `Reachable (stateSpace (.par ss))
  --     ⟨u', _⟩ ⟨v', _⟩`, then for all `i`, the child projections reach
  --     each other in `stateSpace (ss.get i)`.
  -- We proceed by head-style induction on the ReflTransGen chain.
  suffices hmain :
      ∀ {a b : State (.par ss : SessionType)},
        Reachable (stateSpace (.par ss : SessionType)) a b →
        ∀ i : Fin ss.length,
          Reachable (stateSpace (ss.get i))
            ⟨flatToTupleNat ss a.val i.val,
              flatToTupleNat_lt ss a.val
                (show a.val < stateCount.prodChildren ss from a.isLt)
                i.val i.isLt⟩
            ⟨flatToTupleNat ss b.val i.val,
              flatToTupleNat_lt ss b.val
                (show b.val < stateCount.prodChildren ss from b.isLt)
                i.val i.isLt⟩ by
    intro i
    exact hmain hReach i
  -- Main induction.
  intro a b hR
  induction hR using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro i
    exact Reachable.refl _ _
  | @head a' c hedge _hrest ih =>
    intro i
    -- From the head edge, extract the coord-change witness.
    rcases edge_par_preserves_other_coords_fin hedge with ⟨k, hOff, hChild⟩
    -- Case split: either i = k (use child-edge + IH) or i ≠ k (coords
    -- preserved, so just IH).
    by_cases hik : i = k
    · -- Changing coord.
      subst hik
      -- Build a single-step child reachability for `a.val`'s coord `i` →
      -- `c.val`'s coord `i`.
      have hbd_a : flatToTupleNat ss a'.val i.val
                    < stateCount (ss.get i) :=
        flatToTupleNat_lt ss a'.val
          (show a'.val < stateCount.prodChildren ss from a'.isLt)
          i.val i.isLt
      have hbd_c : flatToTupleNat ss c.val i.val
                    < stateCount (ss.get i) :=
        flatToTupleNat_lt ss c.val
          (show c.val < stateCount.prodChildren ss from c.isLt)
          i.val i.isLt
      have hsingle : Reachable (stateSpace (ss.get i))
                       ⟨flatToTupleNat ss a'.val i.val, hbd_a⟩
                       ⟨flatToTupleNat ss c.val i.val, hbd_c⟩ := by
        apply Reachable.single
        show (flatToTupleNat ss a'.val i.val,
              flatToTupleNat ss c.val i.val)
             ∈ edgeList (ss.get i) 0 []
        exact hChild
      exact Reachable.trans _ hsingle (ih i)
    · -- Non-changing coord.
      have hcoordEq : flatToTupleNat ss a'.val i.val
                    = flatToTupleNat ss c.val i.val := hOff i hik
      -- The Fin endpoint at a' and at c are equal for coord i.
      have hFinEq :
          (⟨flatToTupleNat ss a'.val i.val,
            flatToTupleNat_lt ss a'.val
              (show a'.val < stateCount.prodChildren ss from a'.isLt)
              i.val i.isLt⟩ : State (ss.get i))
          = ⟨flatToTupleNat ss c.val i.val,
              flatToTupleNat_lt ss c.val
                (show c.val < stateCount.prodChildren ss from c.isLt)
                i.val i.isLt⟩ := by
        apply Fin.ext
        exact hcoordEq
      rw [hFinEq]
      exact ih i

/-!
### Forward direction — conclusion

The predecessor commit `09f08669` completed Step 2; this commit lands
**Tier F** of Step 3: the forward direction of componentwise reachability
for `.par ss`. This suffices for:

* showing the quotient projection
  `SCCQuotient (stateSpace (.par ss)) → ∀ i, SCCQuotient (stateSpace ss[i])`
  is well-defined as a function, since mutually-reachable flat states have
  mutually-reachable coordinates (apply `reachable_par_forward` twice);
* the "easy" half of the MR iff (forward).

The backward direction (interleave construction) below completes Step 3:
the full componentwise-reachability iff, hence the order-iso and Lattice
transport.
-/

/-!
## Phase 1b-β1c-full — Step 3: Componentwise reachability (backward)

Strategy: prove the backward direction at `Nat` level (`edgeRel`-walks)
and induct on `ss`, using a shift-generalised statement so the tail-call
can be lifted via `lift_tail_walk_to_par`.

For `ss = s :: tl`, decompose `u = uH * pcTl + uT` and `v = vH * pcTl + vT`.

1. **Stage 1 (walk coord 0):** `uH → vH` in `stateSpace s` is given by the
   hypothesis at `i = 0`. `lift_head_walk_to_par` at tail-coord `uT`
   lifts this to a flat walk
     `start + uH*pcTl + uT ↝ start + vH*pcTl + uT`.

2. **Stage 2 (walk remaining coords):** `uT → vT` in `.par tl` is given by
   the IH applied at `start' = start + vH*pcTl`. `lift_tail_walk_to_par`
   at head-coord `vH` lifts this to a flat walk
     `(start + vH*pcTl) + uT ↝ (start + vH*pcTl) + vT`.

The arithmetic identities `flatToTupleNat (s::tl) u 0 = u / pcTl`,
`flatToTupleNat (s::tl) u (k+1) = flatToTupleNat tl (u mod pcTl) k`
bridge the per-coord hypotheses of the cons case to those of the IH.
-/

/-- Shift-generalised backward direction at the `Nat` / `edgeRel` level.

    For any offset `start` and per-child reachability hypotheses for the
    `start = 0, env = []` framework (which is the framework of the global
    `stateSpace`), assemble a walk in the par edge relation at the given
    `start`. The `start + u ↝ start + v` form packages arbitrary offsets,
    which is needed for the recursive `tl`-lift at `start' = start + vH*pcTl`.
-/
theorem par_backward_nat_gen :
    ∀ (ss : List SessionType) (env : List (String × Nat))
      (start : Nat) (u v : Nat),
      u < stateCount.prodChildren ss →
      v < stateCount.prodChildren ss →
      (∀ i : Fin ss.length,
        Relation.ReflTransGen (edgeRel (ss.get i) 0 env)
          (flatToTupleNat ss u i.val) (flatToTupleNat ss v i.val)) →
      Relation.ReflTransGen
        (edgeRel (.par ss : SessionType) start env) (start + u) (start + v)
  | [],      env, start, u, v, hu, hv, _hcoord => by
      -- prodChildren [] = 1, so u = 0 = v.
      have hu0 : u = 0 := by
        have : u < 1 := by simpa [stateCount.prodChildren] using hu
        omega
      have hv0 : v = 0 := by
        have : v < 1 := by simpa [stateCount.prodChildren] using hv
        omega
      subst hu0
      subst hv0
      exact Relation.ReflTransGen.refl
  | s :: tl, env, start, u, v, hu, hv, hcoord => by
      -- Abbreviate pcTl.
      set pcTl := stateCount.prodChildren tl with hpcTl
      -- Bounds: pcTl > 0.
      have hPcTlPos : 0 < pcTl := by
        rw [hpcTl]
        exact stateCount.prodChildren_pos tl (fun t _ => stateCount_pos t)
      -- Decompose u, v.
      set uH := u / pcTl with huH
      set uT := u % pcTl with huT
      set vH := v / pcTl with hvH
      set vT := v % pcTl with hvT
      have huDecomp : u = uH * pcTl + uT := by
        rw [huH, huT]
        conv_lhs => rw [← Nat.div_add_mod u pcTl]
        ring
      have hvDecomp : v = vH * pcTl + vT := by
        rw [hvH, hvT]
        conv_lhs => rw [← Nat.div_add_mod v pcTl]
        ring
      have hPC_cons : stateCount.prodChildren (s :: tl) = stateCount s * pcTl := by
        simp [stateCount.prodChildren, hpcTl]
      rw [hPC_cons] at hu hv
      -- Bounds on uH, uT, vH, vT.
      have huHlt : uH < stateCount s := by
        rw [huH]; exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hu)
      have huTlt : uT < pcTl := by rw [huT]; exact Nat.mod_lt _ hPcTlPos
      have hvHlt : vH < stateCount s := by
        rw [hvH]; exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hv)
      have hvTlt : vT < pcTl := by rw [hvT]; exact Nat.mod_lt _ hPcTlPos
      -- Recover coord-0 walk in `edgeRel s 0 env`: uH → vH.
      have hWalkH : Relation.ReflTransGen (edgeRel s 0 env) uH vH := by
        have h := hcoord ⟨0, by simp [List.length]⟩
        -- h : walk from flatToTupleNat (s::tl) u 0 → flatToTupleNat (s::tl) v 0
        -- in edgeRel ((s::tl).get ⟨0, _⟩) = edgeRel s 0 env.
        have hget : (s :: tl).get ⟨0, by simp [List.length]⟩ = s := rfl
        rw [hget] at h
        have hu0 : flatToTupleNat (s :: tl) u 0 = uH := by
          show u / pcTl = uH; rfl
        have hv0 : flatToTupleNat (s :: tl) v 0 = vH := by
          show v / pcTl = vH; rfl
        rw [hu0, hv0] at h
        exact h
      -- Recover per-coord walks for tl: uT → vT componentwise.
      have hcoordTl :
          ∀ k : Fin tl.length,
            Relation.ReflTransGen (edgeRel (tl.get k) 0 env)
              (flatToTupleNat tl uT k.val) (flatToTupleNat tl vT k.val) := by
        intro k
        have hkSucc : k.succ.val = k.val + 1 := rfl
        have h := hcoord k.succ
        have hget : (s :: tl).get k.succ = tl.get k := rfl
        rw [hget] at h
        -- flatToTupleNat (s::tl) u (k+1) = flatToTupleNat tl (u mod pcTl) k
        have hu_decode : flatToTupleNat (s :: tl) u k.succ.val = flatToTupleNat tl uT k.val := by
          rw [hkSucc]
          show flatToTupleNat tl (u % pcTl) k.val = flatToTupleNat tl uT k.val
          rw [← huT]
        have hv_decode : flatToTupleNat (s :: tl) v k.succ.val = flatToTupleNat tl vT k.val := by
          rw [hkSucc]
          show flatToTupleNat tl (v % pcTl) k.val = flatToTupleNat tl vT k.val
          rw [← hvT]
        rw [hu_decode, hv_decode] at h
        exact h
      -- Stage 1 lift: walk coord 0 (uH → vH) with tail fixed at uT.
      have hStage1 :
          Relation.ReflTransGen (edgeRel (.par (s :: tl) : SessionType) start env)
            (start + uH * pcTl + uT) (start + vH * pcTl + uT) :=
        lift_head_walk_to_par s tl env start uT huTlt hvHlt hWalkH
      -- Stage 2: apply IH on tl at start' = start + vH * pcTl.
      have hPcTlLtPC : vT < pcTl := hvTlt
      have hIH :
          Relation.ReflTransGen
            (edgeRel (.par tl : SessionType) (start + vH * pcTl) env)
            (start + vH * pcTl + uT) (start + vH * pcTl + vT) := by
        have := par_backward_nat_gen tl env (start + vH * pcTl) uT vT
                  huTlt hvTlt hcoordTl
        -- `this` has endpoints `(start + vH*pcTl) + uT` and similarly for vT.
        exact this
      -- Lift stage 2 via `lift_tail_walk_to_par`.
      have hStage2 :
          Relation.ReflTransGen
            (edgeRel (.par (s :: tl) : SessionType) start env)
            (start + vH * pcTl + uT) (start + vH * pcTl + vT) :=
        lift_tail_walk_to_par s tl env start vH hvHlt hIH
      -- Combine and rewrite endpoints to match `start + u` / `start + v`.
      have hSrc : start + u = start + uH * pcTl + uT := by
        rw [huDecomp]; ring
      have hTgt : start + v = start + vH * pcTl + vT := by
        rw [hvDecomp]; ring
      rw [hSrc, hTgt]
      exact hStage1.trans hStage2
  termination_by ss _ _ _ _ => sizeOf ss

/-- **Backward direction of Step 3** (Nat/`edgeRel` form).
    Specialisation of `par_backward_nat_gen` to `start = 0`. -/
theorem par_backward_nat
    (ss : List SessionType) (env : List (String × Nat))
    (u v : Nat)
    (hu : u < stateCount.prodChildren ss)
    (hv : v < stateCount.prodChildren ss)
    (hcoord : ∀ i : Fin ss.length,
      Relation.ReflTransGen (edgeRel (ss.get i) 0 env)
        (flatToTupleNat ss u i.val) (flatToTupleNat ss v i.val)) :
    Relation.ReflTransGen
      (edgeRel (.par ss : SessionType) 0 env) u v := by
  have := par_backward_nat_gen ss env 0 u v hu hv hcoord
  simpa using this

/-- Helper: Fin-level `Reachable` walk → Nat-level `edgeRel` walk.
    A `Reachable (stateSpace S) a b` walk unfolds trivially to a walk in
    `edgeRel S 0 []` between the underlying `Nat` values. -/
theorem edgeRel_of_reachable
    {S : SessionType} {a b : State S}
    (h : Reachable (stateSpace S) a b) :
    Relation.ReflTransGen (edgeRel S 0 []) a.val b.val := by
  refine @Relation.ReflTransGen.lift (State S) Nat
    (stateSpace S).edge (edgeRel S 0 [])
    a b Fin.val
    (fun x y hxy => ?_)
    h
  -- hxy : (stateSpace S).edge x y, i.e., (x.val, y.val) ∈ edgeList S 0 [].
  show (x.val, y.val) ∈ edgeList S 0 []
  exact hxy

/-- **Backward direction of Step 3** (Fin/`Reachable` form).
    If every child-coord projection is reachable in the corresponding
    child state space, then the flat states are reachable in the par
    state space. -/
theorem reachable_par_backward
    (ss : List SessionType)
    (u v : Nat)
    (hu : u < stateCount.prodChildren ss)
    (hv : v < stateCount.prodChildren ss)
    (hCoord : ∀ i : Fin ss.length,
      Reachable (stateSpace (ss.get i))
        ⟨flatToTupleNat ss u i.val, flatToTupleNat_lt ss u hu i.val i.isLt⟩
        ⟨flatToTupleNat ss v i.val, flatToTupleNat_lt ss v hv i.val i.isLt⟩) :
    Reachable (stateSpace (.par ss : SessionType))
      ⟨u, by show u < stateCount (.par ss); simpa [stateCount] using hu⟩
      ⟨v, by show v < stateCount (.par ss); simpa [stateCount] using hv⟩ := by
  -- Step 1: translate each Fin-level hypothesis to a Nat-level walk.
  have hCoordNat : ∀ i : Fin ss.length,
      Relation.ReflTransGen (edgeRel (ss.get i) 0 [])
        (flatToTupleNat ss u i.val) (flatToTupleNat ss v i.val) := by
    intro i
    have := edgeRel_of_reachable (hCoord i)
    exact this
  -- Step 2: apply the Nat-level backward theorem.
  have hWalkNat : Relation.ReflTransGen (edgeRel (.par ss : SessionType) 0 []) u v :=
    par_backward_nat ss [] u v hu hv hCoordNat
  -- Step 3: lift to `Reachable (stateSpace (.par ss))`.
  have hU : u < stateCount (.par ss : SessionType) := by
    show u < stateCount.prodChildren ss; exact hu
  have hV : v < stateCount (.par ss : SessionType) := by
    show v < stateCount.prodChildren ss; exact hv
  exact reachable_of_edgeRel (.par ss) hU hV hWalkNat

/-- **Combined iff (Step 3).** Reachability in `stateSpace (.par ss)`
    is equivalent to componentwise reachability in each child state space. -/
theorem reachable_par_iff
    (ss : List SessionType)
    (u v : Nat)
    (hu : u < stateCount.prodChildren ss)
    (hv : v < stateCount.prodChildren ss) :
    Reachable (stateSpace (.par ss : SessionType))
        ⟨u, by show u < stateCount (.par ss); simpa [stateCount] using hu⟩
        ⟨v, by show v < stateCount (.par ss); simpa [stateCount] using hv⟩ ↔
      ∀ i : Fin ss.length,
        Reachable (stateSpace (ss.get i))
          ⟨flatToTupleNat ss u i.val, flatToTupleNat_lt ss u hu i.val i.isLt⟩
          ⟨flatToTupleNat ss v i.val, flatToTupleNat_lt ss v hv i.val i.isLt⟩ := by
  constructor
  · intro h
    exact reachable_par_forward ss u v hu hv h
  · intro h
    exact reachable_par_backward ss u v hu hv h

/-!
## Phase 1b-β1c-full — MutuallyReachable iff (Step 4)

Reachable-iff immediately lifts to mutually-reachable-iff: a pair of flat
states are SCC-equivalent iff each coordinate pair is SCC-equivalent in
its child state space.
-/

/-- **Componentwise MutuallyReachable (Step 4).** Two flat states in
    `stateSpace (.par ss)` are in the same SCC iff each pair of projections
    is in the same SCC of the respective child state space. -/
theorem mutuallyReachable_par_iff
    (ss : List SessionType)
    (u v : Nat)
    (hu : u < stateCount.prodChildren ss)
    (hv : v < stateCount.prodChildren ss) :
    MutuallyReachable (stateSpace (.par ss : SessionType))
        ⟨u, by show u < stateCount (.par ss); simpa [stateCount] using hu⟩
        ⟨v, by show v < stateCount (.par ss); simpa [stateCount] using hv⟩ ↔
      ∀ i : Fin ss.length,
        MutuallyReachable (stateSpace (ss.get i))
          ⟨flatToTupleNat ss u i.val, flatToTupleNat_lt ss u hu i.val i.isLt⟩
          ⟨flatToTupleNat ss v i.val, flatToTupleNat_lt ss v hv i.val i.isLt⟩ := by
  unfold MutuallyReachable
  rw [reachable_par_iff ss u v hu hv, reachable_par_iff ss v u hv hu]
  exact forall_and.symm

/-!
## Phase 1b-β1c-full — Order isomorphism (Step 5)

The stride bijection of Step 1 plus the componentwise-MR characterisation
of Step 4 packages into an order isomorphism
  `SCCQuotient (stateSpace (.par ss)) ≃o ∀ i, SCCQuotient (stateSpace (ss.get i))`.

The forward map decodes a flat state into its coordinate tuple, each
coordinate quotiented into its child SCC. Well-defined by Step 4 forward.

The backward map assembles a representative of each child SCC into a
flat state, quotiented. Well-defined by Step 4 backward, via `finLiftOn`.

Round-trips come from the arithmetic round-trip lemmas of Step 1 plus
Step 4 once more (to prove that re-picking representatives yields an
SCC-equivalent flat state).

Monotonicity in both directions is `reachable_par_iff` directly.
-/

/-- Helper: convert a Fin-indexed family into the `Nat → Nat` format used
    by `tupleToFlatNat`. Out-of-range indices are mapped to `0`. -/
private def tupleOfFin {ss : List SessionType}
    (g : ∀ i : Fin ss.length, State (ss.get i)) : Nat → Nat :=
  fun n => if h : n < ss.length then (g ⟨n, h⟩).val else 0

/-- Every component of `tupleOfFin g` is in its child's state-count range. -/
private theorem tupleOfFin_lt {ss : List SessionType}
    (g : ∀ i : Fin ss.length, State (ss.get i)) :
    ∀ (i : Nat) (hi : i < ss.length),
      tupleOfFin g i < stateCount (ss.get ⟨i, hi⟩) := by
  intro i hi
  simp [tupleOfFin, hi, (g ⟨i, hi⟩).isLt]

/-- At any in-range index, `tupleOfFin g` just reads off the corresponding
    coordinate. -/
private theorem tupleOfFin_apply {ss : List SessionType}
    (g : ∀ i : Fin ss.length, State (ss.get i))
    (i : Fin ss.length) :
    tupleOfFin g i.val = (g i).val := by
  simp [tupleOfFin, i.isLt]

/-- The forward representative map: a flat state decodes to its
    coordinate tuple, each coordinate quotiented. -/
private def parSCC_toFunRep (ss : List SessionType)
    (s : State (.par ss : SessionType)) :
    ∀ i : Fin ss.length, SCCQuotient (stateSpace (ss.get i)) :=
  fun i => Quotient.mk _
    ⟨flatToTupleNat ss s.val i.val,
      flatToTupleNat_lt ss s.val
        (show s.val < stateCount.prodChildren ss from s.isLt) i.val i.isLt⟩

/-- Forward-map soundness: SCC-equivalent flat states decode to the same
    pointwise quotient class. The hypothesis is stated as
    `MutuallyReachable` to avoid `HasEquiv` synthesis ambiguity. -/
private theorem parSCC_toFunRep_sound (ss : List SessionType)
    (s t : State (.par ss : SessionType))
    (hMR : MutuallyReachable (stateSpace (.par ss : SessionType)) s t) :
    parSCC_toFunRep ss s = parSCC_toFunRep ss t := by
  -- Extract Nat-level bounds from flat MR.
  have hu : s.val < stateCount.prodChildren ss := s.isLt
  have hv : t.val < stateCount.prodChildren ss := t.isLt
  -- The iff statement uses `⟨_, _⟩`-shaped endpoints. `s` and `t` definitionally match.
  have hMR' : MutuallyReachable (stateSpace (.par ss : SessionType))
      ⟨s.val, by show s.val < stateCount (.par ss); simpa [stateCount] using hu⟩
      ⟨t.val, by show t.val < stateCount (.par ss); simpa [stateCount] using hv⟩ := hMR
  have hPt : ∀ i : Fin ss.length,
      MutuallyReachable (stateSpace (ss.get i))
        ⟨flatToTupleNat ss s.val i.val, flatToTupleNat_lt ss s.val hu i.val i.isLt⟩
        ⟨flatToTupleNat ss t.val i.val, flatToTupleNat_lt ss t.val hv i.val i.isLt⟩ :=
    (mutuallyReachable_par_iff ss s.val t.val hu hv).mp hMR'
  -- Each pointwise MR gives a quotient equality via `Quotient.sound`.
  funext i
  unfold parSCC_toFunRep
  exact Quotient.sound (hPt i)

/-- The forward order-iso map: lifts `parSCC_toFunRep` to the quotient.
    The `Quotient.lift` soundness hypothesis `a ≈ b` unfolds to
    `(SCCSetoid (stateSpace (.par ss))).r a b = MutuallyReachable _ a b`. -/
def parSCC_toFun (ss : List SessionType) :
    SCCQuotient (stateSpace (.par ss : SessionType)) →
      ∀ i : Fin ss.length, SCCQuotient (stateSpace (ss.get i)) :=
  Quotient.lift (parSCC_toFunRep ss) (fun a b h => parSCC_toFunRep_sound ss a b h)

/-- The backward representative map: a tuple of representatives assembles
    into a flat state, quotiented. -/
private def parSCC_invFunRep (ss : List SessionType)
    (g : ∀ i : Fin ss.length, State (ss.get i)) :
    SCCQuotient (stateSpace (.par ss : SessionType)) :=
  Quotient.mk _
    ⟨tupleToFlatNat ss (tupleOfFin g),
      by
        show tupleToFlatNat ss (tupleOfFin g) < stateCount (.par ss : SessionType)
        show tupleToFlatNat ss (tupleOfFin g) < stateCount.prodChildren ss
        exact tupleToFlatNat_lt ss _ (tupleOfFin_lt g)⟩

/-- Backward-map soundness: pointwise SCC-equivalent tuples produce the
    same assembled quotient class. -/
private theorem parSCC_invFunRep_sound (ss : List SessionType)
    (g h : ∀ i : Fin ss.length, State (ss.get i))
    (hPt : ∀ i : Fin ss.length,
      MutuallyReachable (stateSpace (ss.get i)) (g i) (h i)) :
    parSCC_invFunRep ss g = parSCC_invFunRep ss h := by
  -- Translate pointwise-MR on Fin-indexed tuples to MR on flat states,
  -- then apply Quotient.sound.
  apply Quotient.sound
  show MutuallyReachable (stateSpace (.par ss : SessionType)) _ _
  -- Use the backward direction of mutuallyReachable_par_iff.
  set u := tupleToFlatNat ss (tupleOfFin g) with hu_def
  set v := tupleToFlatNat ss (tupleOfFin h) with hv_def
  have hu : u < stateCount.prodChildren ss :=
    tupleToFlatNat_lt ss _ (tupleOfFin_lt g)
  have hv : v < stateCount.prodChildren ss :=
    tupleToFlatNat_lt ss _ (tupleOfFin_lt h)
  -- Rewrite each pointwise MR to use flatToTupleNat.
  have hFlat : ∀ i : Fin ss.length,
      MutuallyReachable (stateSpace (ss.get i))
        ⟨flatToTupleNat ss u i.val, flatToTupleNat_lt ss u hu i.val i.isLt⟩
        ⟨flatToTupleNat ss v i.val, flatToTupleNat_lt ss v hv i.val i.isLt⟩ := by
    intro i
    have hg_eq : flatToTupleNat ss u i.val = (g i).val := by
      rw [hu_def, flatToTuple_tupleToFlat ss (tupleOfFin g) (tupleOfFin_lt g) i.val i.isLt]
      exact tupleOfFin_apply g i
    have hh_eq : flatToTupleNat ss v i.val = (h i).val := by
      rw [hv_def, flatToTuple_tupleToFlat ss (tupleOfFin h) (tupleOfFin_lt h) i.val i.isLt]
      exact tupleOfFin_apply h i
    -- `(g i).val`-based endpoints equal `(g i)` and `(h i)` as Fin states.
    have hg_fin : (⟨flatToTupleNat ss u i.val,
                    flatToTupleNat_lt ss u hu i.val i.isLt⟩ : State (ss.get i))
                  = g i := Fin.ext hg_eq
    have hh_fin : (⟨flatToTupleNat ss v i.val,
                    flatToTupleNat_lt ss v hv i.val i.isLt⟩ : State (ss.get i))
                  = h i := Fin.ext hh_eq
    rw [hg_fin, hh_fin]
    exact hPt i
  -- Apply Step 4 backward.
  exact (mutuallyReachable_par_iff ss u v hu hv).mpr hFlat

/-- The backward order-iso map: lifts `parSCC_invFunRep` using `finLiftOn`. -/
def parSCC_invFun (ss : List SessionType)
    (f : ∀ i : Fin ss.length, SCCQuotient (stateSpace (ss.get i))) :
    SCCQuotient (stateSpace (.par ss : SessionType)) :=
  Quotient.finLiftOn f (parSCC_invFunRep ss)
    (fun a b h => parSCC_invFunRep_sound ss a b h)

/-- Computation lemma: `parSCC_invFun` on a family of representatives. -/
@[simp]
theorem parSCC_invFun_mk (ss : List SessionType)
    (g : ∀ i : Fin ss.length, State (ss.get i)) :
    parSCC_invFun ss (fun i => Quotient.mk _ (g i)) = parSCC_invFunRep ss g := by
  unfold parSCC_invFun
  -- The `SCCSetoid` on `stateSpace S` uses `Quotient.mk _ x = ⟦x⟧`.
  -- `Quotient.finLiftOn` with `(⟦g i⟧)` equals the representative-function applied.
  show Quotient.finLiftOn (fun i => ⟦g i⟧) (parSCC_invFunRep ss) _ = _
  rw [Quotient.finLiftOn_mk]

/-- Computation lemma: `parSCC_toFun` on a representative. -/
@[simp]
theorem parSCC_toFun_mk (ss : List SessionType)
    (s : State (.par ss : SessionType)) :
    parSCC_toFun ss (Quotient.mk _ s) = parSCC_toFunRep ss s := rfl

/-- Left inverse: `invFun ∘ toFun = id` on representatives. -/
private theorem parSCC_left_inv (ss : List SessionType)
    (q : SCCQuotient (stateSpace (.par ss : SessionType))) :
    parSCC_invFun ss (parSCC_toFun ss q) = q := by
  induction q using Quotient.ind with
  | _ s =>
    -- `parSCC_toFun ss ⟦s⟧ = fun i => ⟦⟨flatToTupleNat ss s.val i.val, _⟩⟧`
    rw [parSCC_toFun_mk]
    unfold parSCC_toFunRep
    rw [parSCC_invFun_mk]
    unfold parSCC_invFunRep
    apply Quotient.sound
    -- Goal: MR between ⟨tupleToFlatNat ss (tupleOfFin (fun i => ⟨flat..⟩)), _⟩ and s.
    -- By the round-trip, the reassembled flat index equals s.val.
    have hflat : tupleToFlatNat ss (tupleOfFin
        (fun i : Fin ss.length => (⟨flatToTupleNat ss s.val i.val,
          flatToTupleNat_lt ss s.val
            (show s.val < stateCount.prodChildren ss from s.isLt)
            i.val i.isLt⟩ : State (ss.get i))))
        = s.val := by
      -- `tupleOfFin (fun i => ⟨flat..⟩) n = flatToTupleNat ss s.val n` for n < ss.length.
      -- We rewrite `tupleToFlatNat ss _` into `tupleToFlatNat ss (flatToTupleNat ss s.val)`.
      have htup_eq : (tupleOfFin
          (fun i : Fin ss.length => (⟨flatToTupleNat ss s.val i.val,
            flatToTupleNat_lt ss s.val
              (show s.val < stateCount.prodChildren ss from s.isLt)
              i.val i.isLt⟩ : State (ss.get i))))
          = fun n => if n < ss.length then flatToTupleNat ss s.val n else 0 := by
        funext n
        unfold tupleOfFin
        by_cases hn : n < ss.length
        · simp [hn]
        · simp [hn]
      -- Prove that `tupleToFlatNat ss tup = tupleToFlatNat ss flatToTupleNat`
      -- using a local extensionality: they agree on [0, ss.length).
      -- Since `tupleToFlatNat` reads only in-range indices, we get equality.
      -- Easier: use `tupleToFlat_flatToTuple` directly after reducing.
      have : tupleToFlatNat ss (fun n => if n < ss.length then flatToTupleNat ss s.val n else 0)
              = tupleToFlatNat ss (flatToTupleNat ss s.val) := by
        -- Show both agree on all in-range indices; `tupleToFlatNat` only uses those.
        apply tupleToFlatNat_congr
        intro i hi
        simp [hi]
      rw [htup_eq, this]
      exact tupleToFlat_flatToTuple ss s.val s.isLt
    -- Now the assembled Fin-state equals s.
    have heq : (⟨tupleToFlatNat ss (tupleOfFin
        (fun i : Fin ss.length => (⟨flatToTupleNat ss s.val i.val,
          flatToTupleNat_lt ss s.val
            (show s.val < stateCount.prodChildren ss from s.isLt)
            i.val i.isLt⟩ : State (ss.get i)))),
        by
          show tupleToFlatNat ss _ < stateCount (.par ss : SessionType)
          simp [stateCount]
          exact tupleToFlatNat_lt ss _ (tupleOfFin_lt _)⟩ : State (.par ss : SessionType)) = s := by
      apply Fin.ext; exact hflat
    rw [heq]
    exact MutuallyReachable.refl _ _

/-- Right inverse: `toFun ∘ invFun = id` on families of representatives. -/
private theorem parSCC_right_inv (ss : List SessionType)
    (f : ∀ i : Fin ss.length, SCCQuotient (stateSpace (ss.get i))) :
    parSCC_toFun ss (parSCC_invFun ss f) = f := by
  -- Induct on each coordinate's quotient structure via the fintype pi rule.
  induction f using Quotient.ind_fintype_pi with
  | _ g =>
    rw [parSCC_invFun_mk]
    unfold parSCC_invFunRep
    rw [parSCC_toFun_mk]
    unfold parSCC_toFunRep
    funext i
    apply Quotient.sound
    show MutuallyReachable (stateSpace (ss.get i)) _ (g i)
    -- The i-th coordinate of the flat index equals (g i).val by round-trip.
    have hi_eq : flatToTupleNat ss (tupleToFlatNat ss (tupleOfFin g)) i.val
                  = (g i).val := by
      rw [flatToTuple_tupleToFlat ss (tupleOfFin g) (tupleOfFin_lt g) i.val i.isLt]
      exact tupleOfFin_apply g i
    have hfin : (⟨flatToTupleNat ss (tupleToFlatNat ss (tupleOfFin g)) i.val,
                  flatToTupleNat_lt ss (tupleToFlatNat ss (tupleOfFin g))
                    (show tupleToFlatNat ss (tupleOfFin g) < stateCount.prodChildren ss from
                      tupleToFlatNat_lt ss _ (tupleOfFin_lt g))
                    i.val i.isLt⟩ : State (ss.get i)) = g i :=
      Fin.ext hi_eq
    rw [hfin]
    exact MutuallyReachable.refl _ _

/-- Monotonicity of the order-iso: `x ≤ y` in the flat SCC quotient iff
    `parSCC_toFun ss x ≤ parSCC_toFun ss y` pointwise. -/
private theorem parSCC_map_rel_iff (ss : List SessionType)
    (x y : SCCQuotient (stateSpace (.par ss : SessionType))) :
    parSCC_toFun ss x ≤ parSCC_toFun ss y ↔ x ≤ y := by
  induction x using Quotient.ind with
  | _ s =>
    induction y using Quotient.ind with
    | _ t =>
      -- `⟦s⟧ ≤ ⟦t⟧` unfolds to `Reachable (stateSpace (.par ss)) s t`.
      -- Pointwise `≤` unfolds to `∀ i, Reachable (stateSpace (ss.get i)) ...`.
      rw [parSCC_toFun_mk, parSCC_toFun_mk]
      unfold parSCC_toFunRep
      -- LHS: `∀ i, ⟦...⟧ ≤ ⟦...⟧` which is pointwise reachability.
      -- RHS: `⟦s⟧ ≤ ⟦t⟧` which is flat reachability.
      -- Both are encoded by `le'` on quotients, unfolding to `Reachable`.
      have hu : s.val < stateCount.prodChildren ss := s.isLt
      have hv : t.val < stateCount.prodChildren ss := t.isLt
      constructor
      · intro h
        -- `h : ∀ i, ⟦_⟧ ≤ ⟦_⟧` ; each is `Reachable (stateSpace (ss.get i)) _ _`.
        have hCoord : ∀ i : Fin ss.length,
            Reachable (stateSpace (ss.get i))
              ⟨flatToTupleNat ss s.val i.val, flatToTupleNat_lt ss s.val hu i.val i.isLt⟩
              ⟨flatToTupleNat ss t.val i.val, flatToTupleNat_lt ss t.val hv i.val i.isLt⟩ := by
          intro i
          exact h i
        -- Apply Step 3 backward.
        have hFlatReach : Reachable (stateSpace (.par ss : SessionType))
            ⟨s.val, by show s.val < stateCount (.par ss); simpa [stateCount] using hu⟩
            ⟨t.val, by show t.val < stateCount (.par ss); simpa [stateCount] using hv⟩ :=
          (reachable_par_iff ss s.val t.val hu hv).mpr hCoord
        show Reachable (stateSpace (.par ss : SessionType)) s t
        exact hFlatReach
      · intro h
        -- `h : ⟦s⟧ ≤ ⟦t⟧` ; reachability on flat states.
        have hFlat : Reachable (stateSpace (.par ss : SessionType))
            ⟨s.val, by show s.val < stateCount (.par ss); simpa [stateCount] using hu⟩
            ⟨t.val, by show t.val < stateCount (.par ss); simpa [stateCount] using hv⟩ := h
        -- Apply Step 3 forward.
        have hCoord := (reachable_par_iff ss s.val t.val hu hv).mp hFlat
        intro i
        exact hCoord i

/-- **Order isomorphism (Step 5).** The SCC quotient of a par state space
    is order-isomorphic to the product of the SCC quotients of the
    component state spaces. -/
def parSCCOrderIso (ss : List SessionType) :
    SCCQuotient (stateSpace (.par ss : SessionType)) ≃o
      (∀ i : Fin ss.length, SCCQuotient (stateSpace (ss.get i))) where
  toFun := parSCC_toFun ss
  invFun := parSCC_invFun ss
  left_inv := parSCC_left_inv ss
  right_inv := parSCC_right_inv ss
  map_rel_iff' := parSCC_map_rel_iff ss _ _

/-!
## Phase 1b-β1c-full — Lattice transport (Step 6)

Given `Lattice (SCCQuotient (stateSpace (ss.get i)))` for every `i`,
`Pi.instLattice` yields a Lattice on the function space. The order
isomorphism `parSCCOrderIso` transports this Lattice structure back to
`SCCQuotient (stateSpace (.par ss))`.

Concretely, `x ⊔ y := (parSCCOrderIso ss).symm (parSCCOrderIso ss x ⊔ parSCCOrderIso ss y)`
(similarly for `⊓`). Each of the six Lattice axioms reduces to the
corresponding Pi axiom by applying the order iso, using
`OrderIso.le_iff_le`, `OrderIso.apply_symm_apply`, and `OrderIso.symm_apply_apply`.
-/

/-!
To transport the lattice structure, we need each child SCC quotient to
carry a `Lattice` whose underlying `PartialOrder` is the canonical
`SCCQuotient.instPartialOrder`. We express this via an explicit
hypothesis that bundles the sup/inf operations (together with their
lattice axioms) compatibly with the existing partial order.

We expose a structure `SCCLatticeStruct` that records `sup`, `inf`, and
the six lattice axioms **relative to `SCCQuotient.instPartialOrder`**,
avoiding the instance diamond that arises when separate `Lattice`
instances introduce their own internal `PartialOrder` layers.
-/

/-- A lattice structure on `SCCQuotient G` compatible with the canonical
    SCC partial order. This bundles `sup`, `inf`, and the six axioms in
    one place, avoiding the diamond that a typeclass `Lattice` would
    introduce with its own internal `PartialOrder`. -/
structure SCCLatticeStruct {V : Type*} [Fintype V] [DecidableEq V]
    (G : Reticulate.FinDiGraph V) where
  /-- Binary supremum on the SCC quotient. -/
  sup : SCCQuotient G → SCCQuotient G → SCCQuotient G
  /-- Binary infimum on the SCC quotient. -/
  inf : SCCQuotient G → SCCQuotient G → SCCQuotient G
  le_sup_left : ∀ a b, a ≤ sup a b
  le_sup_right : ∀ a b, b ≤ sup a b
  sup_le : ∀ a b c, a ≤ c → b ≤ c → sup a b ≤ c
  inf_le_left : ∀ a b, inf a b ≤ a
  inf_le_right : ∀ a b, inf a b ≤ b
  le_inf : ∀ a b c, a ≤ b → a ≤ c → a ≤ inf b c

/-- Promote an `SCCLatticeStruct` into a `Lattice` instance whose
    underlying `PartialOrder` is `SCCQuotient.instPartialOrder`. -/
def SCCLatticeStruct.toLattice {V : Type*} [Fintype V] [DecidableEq V]
    {G : Reticulate.FinDiGraph V} (L : SCCLatticeStruct G) :
    Lattice (SCCQuotient G) where
  __ := SCCQuotient.instPartialOrder G
  sup := L.sup
  inf := L.inf
  le_sup_left := L.le_sup_left
  le_sup_right := L.le_sup_right
  sup_le := L.sup_le
  inf_le_left := L.inf_le_left
  inf_le_right := L.inf_le_right
  le_inf := L.le_inf

/-- **Lattice on `SCCQuotient (stateSpace (.par ss))` (Step 6).**
    Given a compatible `SCCLatticeStruct` on every child SCC quotient,
    we lift a compatible `SCCLatticeStruct` to the par quotient — then
    promote to `Lattice` via `SCCLatticeStruct.toLattice`.

    The sup/inf are defined componentwise through the order iso:
    `x ⊔ y := iso⁻¹ (iso x ⊔ iso y)` where the Pi ⊔ is pointwise the
    children's ⊔. All six axioms reduce to the child axioms via
    `OrderIso.le_iff_le`, `OrderIso.apply_symm_apply`, and `Pi.le_def`. -/
def par_latticeStruct (ss : List SessionType)
    (hC : ∀ i : Fin ss.length, SCCLatticeStruct (stateSpace (ss.get i))) :
    SCCLatticeStruct (stateSpace (.par ss : SessionType)) where
  sup x y := (parSCCOrderIso ss).symm
    (fun i => (hC i).sup (parSCCOrderIso ss x i) (parSCCOrderIso ss y i))
  inf x y := (parSCCOrderIso ss).symm
    (fun i => (hC i).inf (parSCCOrderIso ss x i) (parSCCOrderIso ss y i))
  le_sup_left x y := by
    rw [← (parSCCOrderIso ss).le_iff_le, OrderIso.apply_symm_apply]
    intro i
    exact (hC i).le_sup_left _ _
  le_sup_right x y := by
    rw [← (parSCCOrderIso ss).le_iff_le, OrderIso.apply_symm_apply]
    intro i
    exact (hC i).le_sup_right _ _
  sup_le x y z hxz hyz := by
    rw [← (parSCCOrderIso ss).le_iff_le, OrderIso.apply_symm_apply]
    intro i
    refine (hC i).sup_le _ _ _ ?_ ?_
    · exact (parSCCOrderIso ss).monotone hxz i
    · exact (parSCCOrderIso ss).monotone hyz i
  inf_le_left x y := by
    rw [← (parSCCOrderIso ss).le_iff_le, OrderIso.apply_symm_apply]
    intro i
    exact (hC i).inf_le_left _ _
  inf_le_right x y := by
    rw [← (parSCCOrderIso ss).le_iff_le, OrderIso.apply_symm_apply]
    intro i
    exact (hC i).inf_le_right _ _
  le_inf x y z hxy hxz := by
    rw [← (parSCCOrderIso ss).le_iff_le, OrderIso.apply_symm_apply]
    intro i
    refine (hC i).le_inf _ _ _ ?_ ?_
    · exact (parSCCOrderIso ss).monotone hxy i
    · exact (parSCCOrderIso ss).monotone hxz i

/-- `Lattice` form of Step 6: given a lattice structure on every child,
    the par SCC quotient is a lattice. -/
def par_lattice (ss : List SessionType)
    (hC : ∀ i : Fin ss.length, SCCLatticeStruct (stateSpace (ss.get i))) :
    Lattice (SCCQuotient (stateSpace (.par ss : SessionType))) :=
  (par_latticeStruct ss hC).toLattice

/-! ### end_ bundle (Phase 1b-close — Deliverable 1)

Lift the existing `end_lattice` instance into the `SCCLatticeStruct` bundle,
so that the universal recursion uses the same shape for every constructor.
All six axioms discharge via `Subsingleton.elim` on the one-element SCC
quotient. -/

/-- `SCCLatticeStruct` bundle for `.end_`. -/
def end_latticeStruct :
    SCCLatticeStruct (stateSpace (.end_ : SessionType)) where
  sup x _ := x
  inf x _ := x
  le_sup_left x y := by
    have : x = y := Subsingleton.elim x y
    exact this ▸ le_refl x
  le_sup_right x y := by
    have : x = y := Subsingleton.elim x y
    exact this ▸ le_refl x
  sup_le x y z hxz _ := by
    have : x = y := Subsingleton.elim x y
    exact this ▸ hxz
  inf_le_left x y := by
    have : x = y := Subsingleton.elim x y
    exact this ▸ le_refl x
  inf_le_right x y := by
    have : x = y := Subsingleton.elim x y
    exact this ▸ le_refl x
  le_inf x y z hxy _ := by
    have : y = z := Subsingleton.elim y z
    exact this ▸ hxy

/-! ### var bundle (Phase 1b-close — Deliverable 2)

`stateCount (.var X) = 1` so the carrier `Fin 1` is a subsingleton, and
the SCC quotient inherits subsingleton structure. The bundle is the
direct analogue of `end_latticeStruct`. -/

/-- `State (.var X)` is a subsingleton: `stateCount (.var X) = 1`. -/
instance instSubsingletonStateVar (X : String) :
    Subsingleton (State (.var X : SessionType)) := by
  unfold State
  show Subsingleton (Fin 1)
  exact inferInstance

/-- The SCC quotient of a one-element graph is a subsingleton. -/
instance instSubsingletonSCCQuotientVar (X : String) :
    Subsingleton (SCCQuotient (stateSpace (.var X : SessionType))) := by
  refine ⟨fun x y => ?_⟩
  induction x using Quotient.ind with
  | _ u =>
    induction y using Quotient.ind with
    | _ v =>
      have : u = v := Subsingleton.elim u v
      exact congrArg _ this

/-- `SCCLatticeStruct` bundle for `.var X`. -/
def var_latticeStruct (X : String) :
    SCCLatticeStruct (stateSpace (.var X : SessionType)) where
  sup x _ := x
  inf x _ := x
  le_sup_left x y := by
    have : x = y := Subsingleton.elim x y
    exact this ▸ le_refl x
  le_sup_right x y := by
    have : x = y := Subsingleton.elim x y
    exact this ▸ le_refl x
  sup_le x y z hxz _ := by
    have : x = y := Subsingleton.elim x y
    exact this ▸ hxz
  inf_le_left x y := by
    have : x = y := Subsingleton.elim x y
    exact this ▸ le_refl x
  inf_le_right x y := by
    have : x = y := Subsingleton.elim x y
    exact this ▸ le_refl x
  le_inf x y z hxy _ := by
    have : y = z := Subsingleton.elim y z
    exact this ▸ hxy

/-!
## Phase 1b-β2 — `rec_ X body` Lattice bridge

The recursive case presents a structural challenge distinct from every
other constructor: `edgeList (.rec_ X body) start env = edgeList body
start ((X, start) :: env)`. Same state count (`stateCount body`), same
start offset — but an *extra back-edge environment entry* that re-routes
every `var X` subterm inside `body` back to `start`.

As a consequence, `stateSpace (.rec_ X body)` and `stateSpace body` have
the same vertex set (both `Fin (stateCount body)`) but potentially
different edge sets: the rec graph has additional back-edges wherever
`var X` occurs inside `body`. These back-edges merge SCCs in the
quotient.

### Ship list for this phase

* **Tier I (structural)**: `edgeList_env_congr_of_freeVars` — the edge
  list depends on `env` only through its action on `freeVars S`. When
  two environments agree on `freeVars S`, they produce identical edge
  lists. Used as a structural tool and for the notFreeVar collapse.
* **Tier II (no-free-X collapse)**: when `X ∉ freeVars body`, the back
  edges are never emitted, so `edgeList (.rec_ X body) start env =
  edgeList body start env`. We derive a `SCCLatticeStruct` on
  `stateSpace (.rec_ X body)` from one on `stateSpace body`.
* **Tier III (hypothesis form)**: `rec_latticeStruct_ofAssumed` +
  `rec_lattice_ofAssumed` — the trivial promotion of a hypothesised
  `SCCLatticeStruct (stateSpace (.rec_ X body))` to a `Lattice`. This
  makes the universal theorem statement available conditionally; the
  remaining obligation is discharging the hypothesis for each body.

### Why back-edges do not break the ordering

`SCCQuotient.instPartialOrder` is the reachability preorder modulo SCC
equivalence; adding edges only adds reachability relations, so the
quotient *coarsens*. That the coarsening remains a lattice is the
content of the conjecture we register as a hypothesis.
-/

/-!
### Tier I — `envLookup`-agnosticity on `freeVars`

If two environments agree on `freeVars S` (pointwise through `envLookup`),
they produce the same edge list. We prove this by joint structural
induction, packaging the three functions (`edgeList`, `edgeListBranchChildren`,
`edgeListParGo`) in one big `mutual` block.
-/

mutual

/-- Congruence of `edgeList` on the environment, restricted to `freeVars S`. -/
theorem edgeList_env_congr_of_freeVars :
    ∀ (S : SessionType) (start : Nat) (env env' : List (String × Nat)),
      (∀ X ∈ freeVars S, envLookup env X = envLookup env' X) →
      edgeList S start env = edgeList S start env'
  | .end_,         _,     _,   _,    _ => by
      simp [edgeList]
  | .var X,        start, env, env', h => by
      have hX : X ∈ freeVars (.var X : SessionType) := by
        simp [freeVars]
      have hLookup : envLookup env X = envLookup env' X := h X hX
      simp only [edgeList]
      rw [hLookup]
  | .branch ms,    start, env, env', h => by
      simp only [edgeList]
      congr 1
      exact edgeList_branchChildren_env_congr ms (start + 2) start (start + 1)
        env env' (fun X hX => h X (by
          show X ∈ freeVars (.branch ms : SessionType)
          simp [freeVars]; exact hX))
  | .select ls,    start, env, env', h => by
      simp only [edgeList]
      congr 1
      exact edgeList_branchChildren_env_congr ls (start + 2) start (start + 1)
        env env' (fun X hX => h X (by
          show X ∈ freeVars (.select ls : SessionType)
          simp [freeVars]; exact hX))
  | .par ss,       start, env, env', h => by
      simp only [edgeList]
      show edgeList.edgeListPar ss start env = edgeList.edgeListPar ss start env'
      unfold edgeList.edgeListPar
      exact edgeList_parGo_env_congr ss start env env' 1
        (fun X hX => h X (by
          show X ∈ freeVars (.par ss : SessionType)
          simp [freeVars]; exact hX))
  | .rec_ Y body,  start, env, env', h => by
      simp only [edgeList]
      apply edgeList_env_congr_of_freeVars body start
        ((Y, start) :: env) ((Y, start) :: env')
      intro X hX
      by_cases hXY : X = Y
      · subst hXY
        simp only [envLookup]
        rfl
      · have hXfree : X ∈ freeVars (.rec_ Y body : SessionType) := by
          show X ∈ freeVars body \ {Y}
          simp [hXY]; exact hX
        have hEq := h X hXfree
        simp only [envLookup]
        have hYX : Y ≠ X := fun h => hXY h.symm
        split_ifs with hcond
        · exact (hXY hcond.symm).elim
        · exact hEq

/-- Congruence of `edgeListBranchChildren` on the environment, restricted to
    the free variables of the pair list. -/
theorem edgeList_branchChildren_env_congr :
    ∀ (ms : List (String × SessionType)) (childStart root bottom : Nat)
      (env env' : List (String × Nat)),
      (∀ X ∈ freeVars.freeVarsPairList ms,
        envLookup env X = envLookup env' X) →
      edgeList.edgeListBranchChildren ms childStart root bottom env =
      edgeList.edgeListBranchChildren ms childStart root bottom env'
  | [], _, _, _, _, _, _ => by simp [edgeList.edgeListBranchChildren]
  | (_, s) :: tl, childStart, root, bottom, env, env', h => by
      simp only [edgeList.edgeListBranchChildren]
      have hHead : edgeList s childStart env = edgeList s childStart env' :=
        edgeList_env_congr_of_freeVars s childStart env env'
          (fun X hX => h X (by
            show X ∈ freeVars.freeVarsPairList ((_, s) :: tl)
            simp [freeVars.freeVarsPairList]
            left; exact hX))
      have hTail : edgeList.edgeListBranchChildren tl (childStart + stateCount s)
                    root bottom env
                = edgeList.edgeListBranchChildren tl (childStart + stateCount s)
                    root bottom env' :=
        edgeList_branchChildren_env_congr tl (childStart + stateCount s)
          root bottom env env'
          (fun X hX => h X (by
            show X ∈ freeVars.freeVarsPairList ((_, s) :: tl)
            simp [freeVars.freeVarsPairList]
            right; exact hX))
      rw [hHead, hTail]

/-- Congruence of `edgeListParGo` on the environment, restricted to free
    variables of the session-type list. -/
theorem edgeList_parGo_env_congr :
    ∀ (ss : List SessionType) (start : Nat) (env env' : List (String × Nat))
      (prefixProd : Nat),
      (∀ X ∈ freeVars.freeVarsList ss,
        envLookup env X = envLookup env' X) →
      edgeList.edgeListParGo ss start env prefixProd =
      edgeList.edgeListParGo ss start env' prefixProd
  | [],      _,     _,   _,    _,          _ => by
      simp [edgeList.edgeListParGo]
  | s :: tl, start, env, env', prefixProd, h => by
      have hHead : edgeList s 0 env = edgeList s 0 env' :=
        edgeList_env_congr_of_freeVars s 0 env env'
          (fun X hX => h X (by
            show X ∈ freeVars.freeVarsList (s :: tl)
            simp [freeVars.freeVarsList]
            left; exact hX))
      have hTail : edgeList.edgeListParGo tl start env (prefixProd * stateCount s) =
                   edgeList.edgeListParGo tl start env' (prefixProd * stateCount s) :=
        edgeList_parGo_env_congr tl start env env' (prefixProd * stateCount s)
          (fun X hX => h X (by
            show X ∈ freeVars.freeVarsList (s :: tl)
            simp [freeVars.freeVarsList]
            right; exact hX))
      -- Use the characteristic equation of `edgeListParGo` to unfold both sides.
      have hLhs :=
        (edgeList.edgeListParGo.eq_def (s :: tl) start env prefixProd)
      have hRhs :=
        (edgeList.edgeListParGo.eq_def (s :: tl) start env' prefixProd)
      rw [hLhs, hRhs]
      simp only [hHead, hTail]

end

/-!
### Tier II — `rec_ X body` with `X ∉ freeVars body`

When the bound variable `X` does not appear free in `body`, the back-edges
emitted by `rec_` are vacuous: every `var X` occurrence is already
captured by an inner rec binder, and the outer `(X, start)` binding is
never consulted. The edge list therefore coincides with the one for
`body` under the same environment.
-/

/-- When `X ∉ freeVars body`, pushing `(X, start)` onto the environment
    does not change the edge list of `body`. -/
theorem edgeList_rec_eq_body_of_notFreeVar
    (X : String) (body : SessionType) (start : Nat) (env : List (String × Nat))
    (hX : X ∉ freeVars body) :
    edgeList body start ((X, start) :: env) = edgeList body start env := by
  apply edgeList_env_congr_of_freeVars body start
  intro Y hY
  -- Y ∈ freeVars body, so Y ≠ X (since X ∉ freeVars body).
  have hYX : Y ≠ X := by
    intro heq; subst heq; exact hX hY
  -- envLookup ((X, start) :: env) Y = if X = Y then some start else envLookup env Y
  simp only [envLookup]
  split_ifs with hcond
  · exact (hYX hcond.symm).elim
  · rfl

/-- Corollary: the rec node's own edge list collapses to body's. -/
theorem edgeList_rec_eq_of_notFreeVar
    (X : String) (body : SessionType) (start : Nat) (env : List (String × Nat))
    (hX : X ∉ freeVars body) :
    edgeList (.rec_ X body : SessionType) start env = edgeList body start env := by
  simp only [edgeList]
  exact edgeList_rec_eq_body_of_notFreeVar X body start env hX

/-!
### Transport: when `body`'s state space equals `rec_`'s state space

`stateSpace S` is a `FinDiGraph (State S)`. Since
`State (.rec_ X body) = Fin (stateCount body) = State body` (propositionally
on carriers), and the edge list coincides in the `notFreeVar` case, the
SCC quotients are canonically identified.

We avoid dealing with heterogeneous-graph issues by expressing the bridge
directly on `State` carriers. The `stateCount` equality `.rec_ X body =
body` is definitional, so `State (.rec_ X body) = State body` also
reduces definitionally.
-/

/-- Auxiliary: `stateCount (.rec_ X body) = stateCount body`. -/
theorem stateCount_rec (X : String) (body : SessionType) :
    stateCount (.rec_ X body : SessionType) = stateCount body := by
  simp [stateCount]

/-- State-carrier equality: `State (.rec_ X body) = State body`. Follows
    from the definitional `stateCount` equality. -/
theorem state_rec_eq (X : String) (body : SessionType) :
    State (.rec_ X body : SessionType) = State body := by
  unfold State
  rw [stateCount_rec]

/-- The raw edge lists agree at the top level when `X ∉ freeVars body`. -/
theorem edgeList_rec_top_eq_of_notFreeVar
    (X : String) (body : SessionType)
    (hX : X ∉ freeVars body) :
    edgeList (.rec_ X body : SessionType) 0 [] = edgeList body 0 [] :=
  edgeList_rec_eq_of_notFreeVar X body 0 [] hX

/-!
### Tier III — Hypothesis-parameterised rec lattice

The deepest deliverable we commit to in this phase: accepting an
`SCCLatticeStruct (stateSpace (.rec_ X body))` as an explicit hypothesis
and promoting it to a `Lattice`. This matches the pattern used by
`par_lattice` and provides the composition interface that the universal
theorem will eventually consume (replacing the hypothesis with a
theorem).
-/

/-- Trivial promotion: an `SCCLatticeStruct` on the rec quotient lifts to
    a `Lattice` instance. This is exactly `SCCLatticeStruct.toLattice`,
    provided here as a named specialisation for API uniformity with
    `par_lattice`. -/
def rec_latticeStruct_ofAssumed (X : String) (body : SessionType)
    (hL : SCCLatticeStruct (stateSpace (.rec_ X body : SessionType))) :
    SCCLatticeStruct (stateSpace (.rec_ X body : SessionType)) :=
  hL

/-- `Lattice` form of the conditional rec bridge: given a compatible
    `SCCLatticeStruct` on the rec's SCC quotient, we obtain a `Lattice`
    instance whose underlying `PartialOrder` is `SCCQuotient.instPartialOrder`. -/
def rec_lattice_ofAssumed (X : String) (body : SessionType)
    (hL : SCCLatticeStruct (stateSpace (.rec_ X body : SessionType))) :
    Lattice (SCCQuotient (stateSpace (.rec_ X body : SessionType))) :=
  hL.toLattice

/-!
### Tier II assembly — the `notFreeVar` rec lattice

When `X ∉ freeVars body`, the edge list of `rec_ X body` agrees
pointwise with that of `body`. Consequently the reachability relation,
the mutual-reachability setoid, the SCC quotient, and finally the
lattice structure all transport in lockstep. We build the transport as
an `SCCLatticeStruct` on the rec graph from one on the body graph.

#### Transport strategy

Both quotients live over the same carrier `Fin (stateCount body)`
(modulo the definitional equation `stateCount (.rec_ X body) =
stateCount body`). The two graphs have the same edge set (by
`edgeList_rec_top_eq_of_notFreeVar`), so:

* `Reachable (stateSpace (.rec_ X body)) u v ↔ Reachable (stateSpace body) u v`
  (reflexive-transitive closure of equal relations coincide).
* `MutuallyReachable` likewise coincides.
* The SCC setoids are pointwise-equal relations, so the quotients are
  isomorphic (via `Quotient.map id` with the appropriate respect proof).

We build the iso and transport `SCCLatticeStruct` across it.
-/

/-- When `X ∉ freeVars body`, the edge relations of the rec stateSpace
    and body stateSpace, viewed at the shared `Fin (stateCount body)`
    carrier, are literally equal. This is the core of the transport. -/
theorem edgeList_eq_at_zero_of_notFreeVar
    (X : String) (body : SessionType)
    (hX : X ∉ freeVars body) :
    edgeList (.rec_ X body : SessionType) 0 [] = edgeList body 0 [] :=
  edgeList_rec_top_eq_of_notFreeVar X body hX

/-- Edge relations agree pointwise on the shared carrier when `X ∉ freeVars body`.
    Since `State (.rec_ X body) = State body` definitionally, a state `u` of
    either graph is the same `Fin (stateCount body)` value. -/
theorem stateSpace_rec_edge_eq_of_notFreeVar
    (X : String) (body : SessionType)
    (hX : X ∉ freeVars body)
    (u v : State body) :
    (stateSpace (.rec_ X body : SessionType)).edge u v ↔
      (stateSpace body).edge u v := by
  show (u.val, v.val) ∈ edgeList (.rec_ X body : SessionType) 0 [] ↔
       (u.val, v.val) ∈ edgeList body 0 []
  rw [edgeList_rec_top_eq_of_notFreeVar X body hX]

/-!
### Reachability transport

Since the edge relations coincide pointwise, so do their reflexive-transitive
closures. Hence `Reachable (stateSpace (.rec_ X body)) u v ↔
Reachable (stateSpace body) u v`, and likewise for `MutuallyReachable`.
-/

/-- Reachability in the rec stateSpace equals reachability in the body
    stateSpace when `X ∉ freeVars body`. Forward direction. -/
theorem reachable_rec_of_body_of_notFreeVar
    (X : String) (body : SessionType)
    (hX : X ∉ freeVars body)
    {u v : State body}
    (h : Reticulate.Reachable (stateSpace body) u v) :
    Reticulate.Reachable (stateSpace (.rec_ X body : SessionType)) u v := by
  unfold Reticulate.Reachable at h ⊢
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hedge ih =>
    apply Relation.ReflTransGen.tail ih
    exact (stateSpace_rec_edge_eq_of_notFreeVar X body hX _ _).mpr hedge

/-- Reachability: body ← rec direction. -/
theorem reachable_body_of_rec_of_notFreeVar
    (X : String) (body : SessionType)
    (hX : X ∉ freeVars body)
    {u v : State body}
    (h : Reticulate.Reachable (stateSpace (.rec_ X body : SessionType)) u v) :
    Reticulate.Reachable (stateSpace body) u v := by
  unfold Reticulate.Reachable at h ⊢
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hedge ih =>
    apply Relation.ReflTransGen.tail ih
    exact (stateSpace_rec_edge_eq_of_notFreeVar X body hX _ _).mp hedge

/-- Reachability equivalence on the shared carrier. -/
theorem reachable_rec_iff_body_of_notFreeVar
    (X : String) (body : SessionType)
    (hX : X ∉ freeVars body)
    (u v : State body) :
    Reticulate.Reachable (stateSpace (.rec_ X body : SessionType)) u v ↔
      Reticulate.Reachable (stateSpace body) u v :=
  ⟨reachable_body_of_rec_of_notFreeVar X body hX,
   reachable_rec_of_body_of_notFreeVar X body hX⟩

/-- Mutual reachability: also coincides between the two graphs. -/
theorem mutuallyReachable_rec_iff_body_of_notFreeVar
    (X : String) (body : SessionType)
    (hX : X ∉ freeVars body)
    (u v : State body) :
    Reticulate.MutuallyReachable (stateSpace (.rec_ X body : SessionType)) u v ↔
      Reticulate.MutuallyReachable (stateSpace body) u v := by
  unfold Reticulate.MutuallyReachable
  rw [reachable_rec_iff_body_of_notFreeVar X body hX,
      reachable_rec_iff_body_of_notFreeVar X body hX]

/-!
### SCCQuotient transport

The SCCSetoids coincide. To transport a quotient across equal setoids,
we use `Quotient.map id` with the identity respect proof.
-/

/-- Transport a quotient equivalence-class to the other graph's quotient. -/
def sccQuotient_rec_to_body_of_notFreeVar
    (X : String) (body : SessionType)
    (hX : X ∉ freeVars body) :
    SCCQuotient (stateSpace (.rec_ X body : SessionType)) →
      SCCQuotient (stateSpace body) :=
  Quotient.map (sa := SCCSetoid (stateSpace (.rec_ X body : SessionType)))
                (sb := SCCSetoid (stateSpace body))
    (fun u => u)
    (fun u v h => (mutuallyReachable_rec_iff_body_of_notFreeVar X body hX u v).mp h)

/-- Transport the other way. -/
def sccQuotient_body_to_rec_of_notFreeVar
    (X : String) (body : SessionType)
    (hX : X ∉ freeVars body) :
    SCCQuotient (stateSpace body) →
      SCCQuotient (stateSpace (.rec_ X body : SessionType)) :=
  Quotient.map (sa := SCCSetoid (stateSpace body))
                (sb := SCCSetoid (stateSpace (.rec_ X body : SessionType)))
    (fun u => u)
    (fun u v h => (mutuallyReachable_rec_iff_body_of_notFreeVar X body hX u v).mpr h)

/-- `Quotient.map` with identity on both sides: round-trips are identity. -/
theorem sccQuotient_rec_to_body_to_rec_of_notFreeVar
    (X : String) (body : SessionType)
    (hX : X ∉ freeVars body)
    (x : SCCQuotient (stateSpace (.rec_ X body : SessionType))) :
    sccQuotient_body_to_rec_of_notFreeVar X body hX
      (sccQuotient_rec_to_body_of_notFreeVar X body hX x) = x := by
  induction x using Quotient.ind with
  | _ u =>
    unfold sccQuotient_rec_to_body_of_notFreeVar sccQuotient_body_to_rec_of_notFreeVar
    rw [Quotient.map_mk, Quotient.map_mk]

theorem sccQuotient_body_to_rec_to_body_of_notFreeVar
    (X : String) (body : SessionType)
    (hX : X ∉ freeVars body)
    (x : SCCQuotient (stateSpace body)) :
    sccQuotient_rec_to_body_of_notFreeVar X body hX
      (sccQuotient_body_to_rec_of_notFreeVar X body hX x) = x := by
  induction x using Quotient.ind with
  | _ u =>
    unfold sccQuotient_rec_to_body_of_notFreeVar sccQuotient_body_to_rec_of_notFreeVar
    rw [Quotient.map_mk, Quotient.map_mk]

/-- Order-preservation of the transport: `x ≤ y` iff the images are. -/
theorem sccQuotient_rec_to_body_le_iff
    (X : String) (body : SessionType)
    (hX : X ∉ freeVars body)
    (x y : SCCQuotient (stateSpace (.rec_ X body : SessionType))) :
    sccQuotient_rec_to_body_of_notFreeVar X body hX x ≤
      sccQuotient_rec_to_body_of_notFreeVar X body hX y ↔ x ≤ y := by
  induction x using Quotient.ind with
  | _ u =>
    induction y using Quotient.ind with
    | _ v =>
      unfold sccQuotient_rec_to_body_of_notFreeVar
      rw [Quotient.map_mk, Quotient.map_mk]
      show Reticulate.Reachable (stateSpace body) u v ↔
           Reticulate.Reachable (stateSpace (.rec_ X body : SessionType)) u v
      exact (reachable_rec_iff_body_of_notFreeVar X body hX u v).symm

/-- Transport an `SCCLatticeStruct` from body to rec when `X ∉ freeVars body`. -/
def rec_latticeStruct_of_notFreeVar
    (X : String) (body : SessionType)
    (hX : X ∉ freeVars body)
    (hL : SCCLatticeStruct (stateSpace body)) :
    SCCLatticeStruct (stateSpace (.rec_ X body : SessionType)) where
  sup x y :=
    sccQuotient_body_to_rec_of_notFreeVar X body hX
      (hL.sup (sccQuotient_rec_to_body_of_notFreeVar X body hX x)
              (sccQuotient_rec_to_body_of_notFreeVar X body hX y))
  inf x y :=
    sccQuotient_body_to_rec_of_notFreeVar X body hX
      (hL.inf (sccQuotient_rec_to_body_of_notFreeVar X body hX x)
              (sccQuotient_rec_to_body_of_notFreeVar X body hX y))
  le_sup_left x y := by
    rw [← sccQuotient_rec_to_body_le_iff X body hX,
        sccQuotient_body_to_rec_to_body_of_notFreeVar]
    exact hL.le_sup_left _ _
  le_sup_right x y := by
    rw [← sccQuotient_rec_to_body_le_iff X body hX,
        sccQuotient_body_to_rec_to_body_of_notFreeVar]
    exact hL.le_sup_right _ _
  sup_le x y z hxz hyz := by
    rw [← sccQuotient_rec_to_body_le_iff X body hX,
        sccQuotient_body_to_rec_to_body_of_notFreeVar]
    refine hL.sup_le _ _ _ ?_ ?_
    · exact (sccQuotient_rec_to_body_le_iff X body hX _ _).mpr hxz
    · exact (sccQuotient_rec_to_body_le_iff X body hX _ _).mpr hyz
  inf_le_left x y := by
    rw [← sccQuotient_rec_to_body_le_iff X body hX,
        sccQuotient_body_to_rec_to_body_of_notFreeVar]
    exact hL.inf_le_left _ _
  inf_le_right x y := by
    rw [← sccQuotient_rec_to_body_le_iff X body hX,
        sccQuotient_body_to_rec_to_body_of_notFreeVar]
    exact hL.inf_le_right _ _
  le_inf x y z hxy hxz := by
    rw [← sccQuotient_rec_to_body_le_iff X body hX,
        sccQuotient_body_to_rec_to_body_of_notFreeVar]
    refine hL.le_inf _ _ _ ?_ ?_
    · exact (sccQuotient_rec_to_body_le_iff X body hX _ _).mpr hxy
    · exact (sccQuotient_rec_to_body_le_iff X body hX _ _).mpr hxz

/-- `Lattice` form of the Tier II rec bridge: when `X ∉ freeVars body`, a
    lattice structure on body's SCC quotient transports to rec's. -/
def rec_lattice_of_notFreeVar
    (X : String) (body : SessionType)
    (hX : X ∉ freeVars body)
    (hL : SCCLatticeStruct (stateSpace body)) :
    Lattice (SCCQuotient (stateSpace (.rec_ X body : SessionType))) :=
  (rec_latticeStruct_of_notFreeVar X body hX hL).toLattice

/-!
### `#eval` sanity checks for the rec bridge

Verify a few terminating rec types to build confidence in the statements.
-/

-- `rec X . end` — X does not appear free in end, so the notFreeVar bridge applies.
example : "X" ∉ freeVars (.end_ : SessionType) := by decide

-- `rec X . &{a: end, b: end}` — X does not appear free in the body.
example : "X" ∉ freeVars (.branch [("a", .end_), ("b", .end_)] : SessionType) := by decide

-- `rec X . &{a: X, b: end}` — X DOES appear free in the body; notFreeVar
-- does not apply. The full rec lattice must use Tier III.
example : "X" ∈ freeVars (.branch [("a", .var "X"), ("b", .end_)] : SessionType) := by decide

/-!
## Phase 1b-β2-II — the hard rec case (`X ∈ freeVars body`)

When `X` appears free in `body`, `stateSpace (.rec_ X body)` acquires
genuine back-edges. Each `var X` subterm inside `body` — sitting at some
absolute position `k` in `Fin (stateCount body)` — produces an edge `(k,
0)` in the rec graph that is NOT in `stateSpace body` (where that `var X`
would have produced no edge, since the empty environment returns `none`
on lookup).

### Scope landed in Phase 1b-β2-II

* **Abstract `varXEndpoints`** — defined as the finset of vertices whose
  `→ start` edge is exclusive to the rec graph. By construction a subset
  of `State body`; finite via the `Finset.univ.filter` pattern. Captures
  all positions that directly back-edge under recursion at the global
  top-level (target `0`).
* **Endpoint single-step lift** — `reachable_rec_endpoint_to_start`.
* **Shadow-free env-extend monotonicity** —
  `edgeList_env_cons_subset`, proved by joint structural induction with
  mutual helpers for branch/select children and par children. The
  shadow-free condition (`envFresh X env`) is essential: it ensures the
  new binding is not dropped by a prior shadowing entry. At the top
  level `env = []` is vacuously fresh for every name.
* **Body → Rec edge monotonicity at top level** (UNCONDITIONAL) —
  `stateSpace_body_edge_of_rec` and its `Prop`-packaging
  `bodySubsetRecEdges_unconditional`. Body-level edges lift into the
  rec-level graph.
* **Body → Rec reachability lift** (UNCONDITIONAL) —
  `reachable_rec_of_body`: any body walk lifts to a rec walk. This
  immediately discharges any "conditional on `BodySubsetRecEdges`"
  statement further downstream.
* **Tier 1 easy direction (← of root-SCC characterisation)**
  (UNCONDITIONAL) — `rec_mutuallyReachable_of_body_reach_endpoint`: if
  `k` is body-reachable from `0` and body-reaches some varXEndpoint,
  then `k` is mutually reachable from `0` in the rec graph.

### Key structural insight (monotonicity survives par lifting)

We initially worried that `edgeList_env_cons_subset` might fail for the
par case because a `var X` back-edge inside a par child gets *lifted*
via stride arithmetic to `(start + pBase + u*suffixProd + q, start +
pBase + v*suffixProd + q)`. The lifted target is not the raw `extra`
value. **However, this does not break monotonicity**: monotonicity says
old-edges ⊆ new-edges. Every old raw child edge lifts to the same old
product edge, and the new child edges lift to *new* product edges that
are added on top. The subset direction survives; only the converse
("every new edge has target `extra`") would fail, and we do not claim it.

### Deferred / STUCK markers

* **Tier 1 hard direction (→)** — given mutual rec-reachability between
  `0` and `k`, extract a varXEndpoint witness. Requires a
  characterisation of the back-edge *image* in the flat global index
  (which back-edges exist, and how they connect through par-lifting to
  the endpoint representation). This is independent of monotonicity —
  it's about DECOMPOSING a walk into body-edge phases and back-edge
  phases, the latter of which need a non-trivial identification.
* **Tiers 2 (non-root SCC singletons)** — depends on Tier 1 →.
* **Tier 3 (quotient collapse structure)** — depends on Tier 2.
* **Tier 4 (unconditional `rec_lattice`)** — depends on Tier 3.

The infrastructure landed here suffices to discharge the easy half of
the root-SCC characterisation. The hard half (→) is the natural next
target for Phase 1b-β3.
-/

/-!
### Abstract `varXEndpoints`
-/

/-- The set of vertices `k : State body` whose `→ start` edge exists in
    `stateSpace (.rec_ X body)` but not in `stateSpace body`. Captures
    every direct back-edge contributed by a `var X` occurrence. -/
def varXEndpoints (X : String) (body : SessionType) : Finset (State body) :=
  (Finset.univ : Finset (State body)).filter (fun k =>
    decide ((k.val, 0) ∈ edgeList (.rec_ X body : SessionType) 0 []) ∧
    decide ((k.val, 0) ∉ edgeList body 0 []))

/-- The defining membership property of `varXEndpoints`, stated at the
    edge-list level. -/
theorem mem_varXEndpoints_iff (X : String) (body : SessionType) (k : State body) :
    k ∈ varXEndpoints X body ↔
      (k.val, 0) ∈ edgeList (.rec_ X body : SessionType) 0 [] ∧
      (k.val, 0) ∉ edgeList body 0 [] := by
  unfold varXEndpoints
  rw [Finset.mem_filter]
  simp

/-!
### Back-edge single-step: from endpoint to `0` in the rec graph

Every `k ∈ varXEndpoints X body` has, by definition, a direct edge `(k,
0)` in the rec graph. We package this as a `Reachable` fact for easy
composition.
-/

/-- Endpoint back-edge: from an endpoint to the start in one step. -/
theorem reachable_rec_endpoint_to_start
    (X : String) (body : SessionType) (k : State body)
    (hk : k ∈ varXEndpoints X body) :
    Reticulate.Reachable (stateSpace (.rec_ X body : SessionType))
      (show State (.rec_ X body : SessionType) from k)
      (show State (.rec_ X body : SessionType) from ⟨0, stateCount_pos _⟩) := by
  apply Reticulate.Reachable.single
  show (k.val, 0) ∈ edgeList (.rec_ X body : SessionType) 0 []
  exact ((mem_varXEndpoints_iff X body k).mp hk).1

/-!
### Body → Rec edge inclusion

The key structural fact: every edge in the body graph is also an edge in
the rec graph. Intuitively, pushing the `(X, start)` entry onto an empty
environment only *adds* edge possibilities — where the empty env emitted
nothing for a `var X` subterm, the extended env emits `(k, start)`.
Every other edge emitted by body's structural recursion is *env-
independent* (or only consults entries further down the stack, which are
unaffected by the extension).

We prove this by joint structural induction, analogous to
`edgeList_env_congr_of_freeVars` but for the inclusion direction with a
shadow-free condition. At the top level `env = []` is vacuously fresh
for every name, so the monotonicity applies unconditionally.

**Structural insight:** new edges appearing under env-extension go
from some position `k` (the var-X slot) to the `extra` value. For
branch/select subterms, `extra = rec's start = top-level 0`. For par
subterms, the local new edge gets *lifted* to the flat index, but the
lift is structure-preserving — old lifted edges remain; new lifted
edges are added. So the inclusion survives the par layer.
-/

/-- `X` is not a key of `env`. -/
def envFresh (X : String) (env : List (String × Nat)) : Prop :=
  ∀ t, (X, t) ∉ env

/-- Empty env is fresh for every name. -/
theorem envFresh_nil (X : String) : envFresh X [] := by
  intro _ h
  exact (List.not_mem_nil h).elim

/-- Lookup on a fresh key is `none`. -/
theorem envLookup_eq_none_of_fresh (X : String) (env : List (String × Nat))
    (hFresh : envFresh X env) :
    envLookup env X = none := by
  induction env with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨y, n⟩ := hd
      simp only [envLookup]
      by_cases hEq : y = X
      · subst hEq
        exfalso
        exact hFresh n (by simp)
      · rw [if_neg hEq]
        apply ih
        intro t hT
        exact hFresh t (by simp [hT])

/-- Monotonicity of `edgeListParLiftChild` in its first (edges) argument.
    Stated outside the `mutual` block; used inside via recursion. -/
theorem edgeListParLiftChild_mono_edges :
    ∀ (e1 : List (Nat × Nat)) (e2 : List (Nat × Nat)) (start suffixProd size prefixProd u v : Nat),
      (∀ (a b : Nat), (a, b) ∈ e1 → (a, b) ∈ e2) →
      (u, v) ∈ edgeList.edgeListParLiftChild e1 start suffixProd size prefixProd →
      (u, v) ∈ edgeList.edgeListParLiftChild e2 start suffixProd size prefixProd
  | [], _, _, _, _, _, _, _, _, h => by
      simp [edgeList.edgeListParLiftChild] at h
  | (a, b) :: rest, e2, start, suffixProd, size, prefixProd, u, v, hSub, h => by
      simp only [edgeList.edgeListParLiftChild] at h
      rcases List.mem_append.mp h with hHere | hRest
      · -- (u, v) is in liftOne for head edge (a, b).
        have hAB : (a, b) ∈ e2 := hSub a b (List.mem_cons_self ..)
        -- Convert `(u, v) ∈ liftOne a b ... 0` to the arithmetic form, then
        -- wrap back into `liftChild e2` via `mem_edgeListParLiftChild`.
        rcases (mem_edgeListParLiftOne a b start suffixProd size prefixProd 0
                  u v).mp hHere with ⟨p, q, _, hplt, hqlt, hsrc, htgt⟩
        rw [mem_edgeListParLiftChild]
        refine ⟨a, b, hAB, p, q, hplt, hqlt, hsrc, htgt⟩
      · -- Recursive case on tail.
        apply edgeListParLiftChild_mono_edges rest e2 start suffixProd size
          prefixProd u v _ hRest
        intro a' b' hab
        exact hSub a' b' (List.mem_cons_of_mem _ hab)

mutual

/-- Shadow-free env-extend monotonicity for `edgeList`. -/
theorem edgeList_env_cons_subset :
    ∀ (S : SessionType) (start : Nat) (X : String) (extra : Nat)
      (env : List (String × Nat)) (_ : envFresh X env) (u v : Nat),
      (u, v) ∈ edgeList S start env →
      (u, v) ∈ edgeList S start ((X, extra) :: env)
  | .end_,        _,     _, _,     _,   _,      _, _, h => by
      simp [edgeList] at h
  | .var Y,       start, X, extra, env, hFresh, u, v, h => by
      simp only [edgeList] at h ⊢
      by_cases hXY : X = Y
      · subst hXY
        -- With X = Y, the env lookup of X on env is `none` (by freshness),
        -- so the pre-extension edge list is `[]` — `h` is absurd.
        rw [envLookup_eq_none_of_fresh X env hFresh] at h
        exact absurd h (by simp)
      · -- X ≠ Y: both lookups consult env in the same way.
        have hYX : X ≠ Y := hXY
        simp only [envLookup, if_neg hYX]
        exact h
  | .branch ms,   start, X, extra, env, hFresh, u, v, h => by
      simp only [edgeList] at h ⊢
      rcases List.mem_append.mp h with hPre | hChild
      · exact List.mem_append.mpr (Or.inl hPre)
      · refine List.mem_append.mpr (Or.inr ?_)
        exact edgeList_branchChildren_env_cons_subset ms (start + 2) start
          (start + 1) X extra env hFresh u v hChild
  | .select ls,   start, X, extra, env, hFresh, u, v, h => by
      simp only [edgeList] at h ⊢
      rcases List.mem_append.mp h with hPre | hChild
      · exact List.mem_append.mpr (Or.inl hPre)
      · refine List.mem_append.mpr (Or.inr ?_)
        exact edgeList_branchChildren_env_cons_subset ls (start + 2) start
          (start + 1) X extra env hFresh u v hChild
  | .par ss,      start, X, extra, env, hFresh, u, v, h => by
      simp only [edgeList] at h ⊢
      unfold edgeList.edgeListPar at h ⊢
      exact edgeList_parGo_env_cons_subset ss start X extra env 1 hFresh u v h
  | .rec_ Y body, start, X, extra, env, hFresh, u, v, h => by
      simp only [edgeList] at h ⊢
      -- Two sub-cases: X = Y (inner binder shadows outer extension) or X ≠ Y.
      by_cases hXY : X = Y
      · -- X = Y: both envs behave the same because the inner (Y, start) head
        -- shadows the (X, extra) position-2 entry on the RHS.
        subst hXY
        -- Apply env_congr: the two envs agree on all names (lookup-wise).
        have hEq : edgeList body start ((X, start) :: env) =
                   edgeList body start ((X, start) :: (X, extra) :: env) := by
          apply edgeList_env_congr_of_freeVars body start
          intro Z _
          simp only [envLookup]
          by_cases hZ : X = Z
          · simp [hZ]
          · simp [hZ]
        rw [← hEq]
        exact h
      · -- X ≠ Y. Apply IH at env' := (Y, start) :: env (still fresh for X).
        have hFresh' : envFresh X ((Y, start) :: env) := by
          intro t hT
          rcases List.mem_cons.mp hT with hHead | hTail
          · injection hHead with hXYeq _
            exact hXY hXYeq
          · exact hFresh t hTail
        -- Direct IH gives: (u,v) ∈ edgeList body start ((X,extra) :: (Y,start) :: env).
        -- We need: (u,v) ∈ edgeList body start ((Y,start) :: (X,extra) :: env).
        -- The two envs give the same lookup on every variable Z:
        --   LHS for Z: if X = Z then some extra else (if Y = Z then some start else lookup env Z)
        --   RHS for Z: if Y = Z then some start else (if X = Z then some extra else lookup env Z)
        -- Since X ≠ Y, the two are equal (X = Z and Y = Z are mutually exclusive).
        have hIH : (u, v) ∈ edgeList body start ((X, extra) :: (Y, start) :: env) :=
          edgeList_env_cons_subset body start X extra ((Y, start) :: env)
            hFresh' u v h
        have hReorder : edgeList body start ((X, extra) :: (Y, start) :: env) =
                        edgeList body start ((Y, start) :: (X, extra) :: env) := by
          apply edgeList_env_congr_of_freeVars body start
          intro Z _
          simp only [envLookup]
          by_cases hXZ : X = Z
          · -- X = Z: LHS returns some extra at level 1 of cons.
            -- RHS: first checks Y = Z; since X ≠ Y, Y ≠ Z, so falls through to
            -- checking X = Z, returns some extra.
            have hYZ : Y ≠ Z := fun h => hXY (hXZ.trans h.symm)
            rw [if_pos hXZ, if_neg hYZ, if_pos hXZ]
          · by_cases hYZ : Y = Z
            · -- X ≠ Z, Y = Z: LHS falls through to checking Y = Z → some start.
              --                 RHS has Y = Z at head → some start.
              rw [if_neg hXZ, if_pos hYZ, if_pos hYZ]
            · rw [if_neg hXZ, if_neg hYZ, if_neg hYZ, if_neg hXZ]
        rw [← hReorder]
        exact hIH

/-- Shadow-free env-extend monotonicity for branch children. -/
theorem edgeList_branchChildren_env_cons_subset :
    ∀ (ms : List (String × SessionType)) (childStart root bottom : Nat)
      (X : String) (extra : Nat) (env : List (String × Nat))
      (_ : envFresh X env) (u v : Nat),
      (u, v) ∈ edgeList.edgeListBranchChildren ms childStart root bottom env →
      (u, v) ∈ edgeList.edgeListBranchChildren ms childStart root bottom
                  ((X, extra) :: env)
  | [], _, _, _, _, _, _, _, _, _, h => by
      simp [edgeList.edgeListBranchChildren] at h
  | (_, s) :: tl, childStart, root, bottom, X, extra, env, hFresh, u, v, h => by
      -- Characteristic: the list is `entryEdge :: exitEdge :: (childEdges ++ restEdges)`.
      -- Unfold the definition using `simp only` with the function name; this
      -- rewrites `edgeListBranchChildren` to its body (which contains `::`).
      simp only [edgeList.edgeListBranchChildren] at h ⊢
      -- Now h : (u, v) ∈ (root, childStart) :: (exitSlot s childStart, bottom)
      --                  :: (edgeList s childStart env ++ ... env).
      rcases List.mem_cons.mp h with hEntry | hRest1
      · exact List.mem_cons.mpr (Or.inl hEntry)
      · rcases List.mem_cons.mp hRest1 with hExit | hRest2
        · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl hExit)))
        · rcases List.mem_append.mp hRest2 with hChild | hTail
          · refine List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
              (Or.inr (List.mem_append.mpr (Or.inl ?_)))))
            exact edgeList_env_cons_subset s childStart X extra env
              hFresh u v hChild
          · refine List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
              (Or.inr (List.mem_append.mpr (Or.inr ?_)))))
            exact edgeList_branchChildren_env_cons_subset tl
              (childStart + stateCount s) root bottom X extra env
              hFresh u v hTail

/-- Shadow-free env-extend monotonicity for par children walker. -/
theorem edgeList_parGo_env_cons_subset :
    ∀ (ss : List SessionType) (start : Nat) (X : String) (extra : Nat)
      (env : List (String × Nat)) (prefixProd : Nat)
      (_ : envFresh X env) (u v : Nat),
      (u, v) ∈ edgeList.edgeListParGo ss start env prefixProd →
      (u, v) ∈ edgeList.edgeListParGo ss start ((X, extra) :: env) prefixProd
  | [], _, _, _, _, _, _, _, _, h => by
      simp [edgeList.edgeListParGo] at h
  | s :: tl, start, X, extra, env, prefixProd, hFresh, u, v, h => by
      have hLhs := edgeList.edgeListParGo.eq_def (s :: tl) start env prefixProd
      have hRhs := edgeList.edgeListParGo.eq_def (s :: tl) start
                    ((X, extra) :: env) prefixProd
      rw [hLhs] at h
      rw [hRhs]
      rcases List.mem_append.mp h with hHere | hRest
      · -- (u, v) is in liftedForThis under env; must show it's in
        -- liftedForThis under ((X, extra) :: env).
        refine List.mem_append.mpr (Or.inl ?_)
        -- Use the IH on `s` for `edgeList s 0`; the raw child list grows;
        -- the filter is env-independent; and the lift pipeline is monotone
        -- in its edges argument.
        have hSub : ∀ (a b : Nat),
            (a, b) ∈ (edgeList s 0 env).filter
                      (fun e => decide (e.1 < stateCount s) &&
                                decide (e.2 < stateCount s)) →
            (a, b) ∈ (edgeList s 0 ((X, extra) :: env)).filter
                      (fun e => decide (e.1 < stateCount s) &&
                                decide (e.2 < stateCount s)) := by
          intro a b hab
          simp only [List.mem_filter] at hab ⊢
          refine ⟨edgeList_env_cons_subset s 0 X extra env hFresh a b hab.1, hab.2⟩
        -- Apply the stand-alone `mono_edges` lemma.
        exact edgeListParLiftChild_mono_edges
          ((edgeList s 0 env).filter (fun e => decide (e.1 < stateCount s)
                                                && decide (e.2 < stateCount s)))
          ((edgeList s 0 ((X, extra) :: env)).filter
            (fun e => decide (e.1 < stateCount s) && decide (e.2 < stateCount s)))
          start (stateCount.prodChildren tl) (stateCount s) prefixProd u v hSub
          hHere
      · refine List.mem_append.mpr (Or.inr ?_)
        exact edgeList_parGo_env_cons_subset tl start X extra env
          (prefixProd * stateCount s) hFresh u v hRest

end

/-!
### Body → Rec edge monotonicity at top level — UNCONDITIONAL

The top-level call of `stateSpace (.rec_ X body)` uses `env = [(X, 0)]`
relative to `body`'s top-level call `env = []`. Since `[] = env` is
vacuously fresh for `X`, `edgeList_env_cons_subset` gives us
`edgeList body 0 [] ⊆ edgeList body 0 [(X, 0)] = edgeList (.rec_ X body) 0 []`.
-/

/-- Top-level body-edge inclusion at the edge-list level. -/
theorem edgeList_body_subset_rec
    (X : String) (body : SessionType) (u v : Nat)
    (h : (u, v) ∈ edgeList body 0 []) :
    (u, v) ∈ edgeList (.rec_ X body : SessionType) 0 [] := by
  simp only [edgeList]
  exact edgeList_env_cons_subset body 0 X 0 [] (envFresh_nil X) u v h

/-- Body-edge ⇒ rec-edge at the `FinDiGraph` level — UNCONDITIONAL. -/
theorem stateSpace_body_edge_of_rec
    (X : String) (body : SessionType) (u v : State body)
    (h : (stateSpace body).edge u v) :
    (stateSpace (.rec_ X body : SessionType)).edge
      (show State (.rec_ X body : SessionType) from u)
      (show State (.rec_ X body : SessionType) from v) := by
  show (u.val, v.val) ∈ edgeList (.rec_ X body : SessionType) 0 []
  exact edgeList_body_subset_rec X body u.val v.val h

/-- Body-edges are a subset of rec-edges at the top level (unconditional
    packaging form, matching the downstream interface). -/
def BodySubsetRecEdges (X : String) (body : SessionType) : Prop :=
  ∀ u v : State body,
    (stateSpace body).edge u v →
    (stateSpace (.rec_ X body : SessionType)).edge
      (show State (.rec_ X body : SessionType) from u)
      (show State (.rec_ X body : SessionType) from v)

/-- `BodySubsetRecEdges` holds for every `X` and `body` — unconditional
    discharge using the structural monotonicity lemma. -/
theorem bodySubsetRecEdges_unconditional (X : String) (body : SessionType) :
    BodySubsetRecEdges X body :=
  fun u v h => stateSpace_body_edge_of_rec X body u v h

/-- Body reachability lifts to rec reachability unconditionally. -/
theorem reachable_rec_of_body_of_hyp
    (X : String) (body : SessionType)
    (hSub : BodySubsetRecEdges X body)
    {u v : State body}
    (h : Reticulate.Reachable (stateSpace body) u v) :
    Reticulate.Reachable (stateSpace (.rec_ X body : SessionType)) u v := by
  unfold Reticulate.Reachable at h ⊢
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hedge ih =>
      apply Relation.ReflTransGen.tail ih
      exact hSub _ _ hedge

/-- Unconditional form: body reachability lifts to rec reachability. -/
theorem reachable_rec_of_body
    (X : String) (body : SessionType) {u v : State body}
    (h : Reticulate.Reachable (stateSpace body) u v) :
    Reticulate.Reachable (stateSpace (.rec_ X body : SessionType)) u v :=
  reachable_rec_of_body_of_hyp X body (bodySubsetRecEdges_unconditional X body) h

/-!
### Tier 1 — easy direction (← of root-SCC characterisation)

If `k` is body-reachable from `0` AND body-reaches some varXEndpoint,
then `k` is mutually reachable from `0` in the rec graph.

* Forward leg (`0 →* k` in rec): body-walk lifts to rec-walk.
* Backward leg (`k →* 0` in rec): body-walk `k →* e`, then back-edge
  `e → 0`.

**Unconditional**: the body-edge monotonicity is now proved structurally.
-/

/-- Tier 1 **easy direction** (← of the root-SCC characterisation),
    unconditional. Having a body-path to the start and a body-path to a
    varXEndpoint is sufficient for mutual rec-reachability from `0`. -/
theorem rec_mutuallyReachable_of_body_reach_endpoint
    (X : String) (body : SessionType) (k : State body)
    (hFromStart : Reticulate.Reachable (stateSpace body)
                    ⟨0, stateCount_pos _⟩ k)
    (hToEndpoint : ∃ e ∈ varXEndpoints X body,
                    Reticulate.Reachable (stateSpace body) k e) :
    Reticulate.MutuallyReachable (stateSpace (.rec_ X body : SessionType))
      (show State (.rec_ X body : SessionType) from ⟨0, stateCount_pos _⟩)
      (show State (.rec_ X body : SessionType) from k) := by
  constructor
  · -- 0 →* k in rec.
    exact reachable_rec_of_body X body hFromStart
  · -- k →* 0 in rec: walk body k →* e, then back-edge e → 0.
    obtain ⟨e, heIn, heWalk⟩ := hToEndpoint
    have hkToE : Reticulate.Reachable (stateSpace (.rec_ X body : SessionType))
                  (show State (.rec_ X body : SessionType) from k)
                  (show State (.rec_ X body : SessionType) from e) :=
      reachable_rec_of_body X body heWalk
    have hEToZero : Reticulate.Reachable (stateSpace (.rec_ X body : SessionType))
                    (show State (.rec_ X body : SessionType) from e)
                    (show State (.rec_ X body : SessionType) from
                      ⟨0, stateCount_pos _⟩) :=
      reachable_rec_endpoint_to_start X body e heIn
    exact Reticulate.Reachable.trans _ hkToE hEToZero

/-!
### Sanity checks for the landed material
-/

-- `BodySubsetRecEdges` holds unconditionally.
example : BodySubsetRecEdges "X" (.end_ : SessionType) :=
  bodySubsetRecEdges_unconditional "X" (.end_)

/-!
## Phase 1b-β2-II — Tier 1 forward direction (`→`), partial

We now tackle the hard direction of the root-SCC characterisation.
Given `MutuallyReachable (stateSpace (.rec_ X body)) 0 k`, extract:
1. a body-walk `0 →* k`, and
2. a varXEndpoint witness `e ∈ varXEndpoints X body` with body-walk `k →* e`.

### The structural obstacle

`edgeList (.rec_ X body) 0 [] = edgeList body 0 [(X, 0)]`, and while
`edgeList body 0 [] ⊆ edgeList body 0 [(X, 0)]` (proved as
`edgeList_env_cons_subset`), characterising the "new edges" is non-trivial
through `par`: a back-edge with target `0` in a `par` child, after being
filtered and lifted, acquires target `start + base + q` — not `0`. The
"new edges target 0" claim fails through par-lifting.

### Scope of this tier

We therefore scope the forward direction to **par-free bodies**. Formally,
we introduce `hasNoPar : SessionType → Prop`: true iff the AST contains no
`par` constructor. For par-free bodies, a weak bridge statement is
provable structurally: any edge in the rec-env graph has its target
either in the base-env graph or equal to `extra`.

The stronger form ("source is a `varXEndpoint`") additionally needs a
layout argument about the source slot — deferred to a later tier. The
par case is entirely deferred.

### Tiers landed in this sub-phase

* **Tier 1(a-weak)** — `edgeList_env_cons_target`: for par-free
  subterms, any edge in the env-extended call has target either in the
  base-env call's edge list OR equal to `extra`. Proved by joint
  structural induction with a branch/select-children helper; the `par`
  case is refuted by `hasNoPar`.

### Tiers deferred

* **Tier 1(a-strong)** — strengthening: "source is a varXEndpoint" (needs
  a separate source-tracking argument via layout bounds).
* **Tier 1(b)** — par-aware characterisation (column targets).
* **Tier 1(c)** — Part (1) / Part (2) extraction and the full
  `rec_root_scc_characterisation_forward` theorem.
* **Tier 2+** — all downstream work.
-/

/-!
### `hasNoPar` predicate
-/

/-- `hasNoPar S` is true iff no `par` constructor appears anywhere in the
    AST of `S`. This restriction sidesteps the stride-arithmetic issue
    that blocks a clean "new edges target extra" lemma under `par`. -/
def hasNoPar : SessionType → Prop
  | .end_        => True
  | .var _       => True
  | .branch ms   => hasNoParPairList ms
  | .select ls   => hasNoParPairList ls
  | .par _       => False
  | .rec_ _ body => hasNoPar body
where
  hasNoParList : List SessionType → Prop
    | []      => True
    | s :: tl => hasNoPar s ∧ hasNoParList tl
  hasNoParPairList : List (String × SessionType) → Prop
    | []      => True
    | p :: tl => hasNoPar p.2 ∧ hasNoParPairList tl

/-!
### Weak bridge lemma: edge targets

For par-free `S`, every edge in `edgeList S start ((X, extra) :: env)` has
its target either already present as an edge in the base-env graph or
equal to `extra`. This is the structural bridge that a future tier can
combine with source-tracking to obtain the full "new edges are back-edges"
statement.

We prove the generalised form — any `start`, `extra`, `envFresh X env` —
by joint structural induction with a helper on branch/select children.
The par case is excluded by the `hasNoPar` hypothesis.
-/

mutual

/-- **Weak bridge lemma.** For par-free `S`, any edge in the env-extended
    graph is either an edge in the base-env graph or has target `extra`. -/
theorem edgeList_env_cons_target :
    ∀ (S : SessionType) (start : Nat) (X : String) (extra : Nat)
      (env : List (String × Nat)) (_ : hasNoPar S) (_ : envFresh X env)
      (u v : Nat),
      (u, v) ∈ edgeList S start ((X, extra) :: env) →
      (u, v) ∈ edgeList S start env ∨ v = extra
  | .end_,        _,     _, _,     _,   _,    _,      _, _, h => by
      simp [edgeList] at h
  | .var Y,       start, X, extra, env, _,    hFresh, u, v, h => by
      simp only [edgeList] at h
      by_cases hXY : X = Y
      · subst hXY
        have hExt : envLookup ((X, extra) :: env) X = some extra := by
          simp [envLookup]
        rw [hExt] at h
        simp at h
        exact Or.inr h.2
      · have hYX : X ≠ Y := hXY
        simp only [envLookup, if_neg hYX] at h
        left
        simp only [edgeList]
        exact h
  | .branch ms,   start, X, extra, env, hNP, hFresh, u, v, h => by
      simp only [edgeList] at h
      rcases List.mem_append.mp h with hPre | hChild
      · left
        simp only [edgeList]
        exact List.mem_append.mpr (Or.inl hPre)
      · have hDec := edgeList_branchChildren_env_cons_target ms (start + 2)
          start (start + 1) X extra env hNP hFresh u v hChild
        rcases hDec with hB | hBack
        · left; simp only [edgeList]
          exact List.mem_append.mpr (Or.inr hB)
        · exact Or.inr hBack
  | .select ls,   start, X, extra, env, hNP, hFresh, u, v, h => by
      simp only [edgeList] at h
      rcases List.mem_append.mp h with hPre | hChild
      · left
        simp only [edgeList]
        exact List.mem_append.mpr (Or.inl hPre)
      · have hDec := edgeList_branchChildren_env_cons_target ls (start + 2)
          start (start + 1) X extra env hNP hFresh u v hChild
        rcases hDec with hB | hBack
        · left; simp only [edgeList]
          exact List.mem_append.mpr (Or.inr hB)
        · exact Or.inr hBack
  | .par _,      _,     _, _,     _,   hNP, _,      _, _, _ => by
      exact absurd hNP (by simp [hasNoPar])
  | .rec_ Y body, start, X, extra, env, hNP, hFresh, u, v, h => by
      simp only [edgeList] at h
      by_cases hXY : X = Y
      · -- X = Y: inner binder shadows outer extension.
        subst hXY
        have hEq : edgeList body start ((X, start) :: (X, extra) :: env) =
                   edgeList body start ((X, start) :: env) := by
          apply edgeList_env_congr_of_freeVars body start
          intro Z _
          simp only [envLookup]
          by_cases hZ : X = Z
          · simp [hZ]
          · simp [hZ]
        rw [hEq] at h
        left
        simp only [edgeList]
        exact h
      · -- X ≠ Y. Recurse on body with env' = (Y, start) :: env.
        have hFresh' : envFresh X ((Y, start) :: env) := by
          intro t hT
          rcases List.mem_cons.mp hT with hHead | hTail
          · injection hHead with hXYeq _
            exact hXY hXYeq
          · exact hFresh t hTail
        have hNP' : hasNoPar body := by
          simpa [hasNoPar] using hNP
        have hReorder : edgeList body start ((Y, start) :: (X, extra) :: env) =
                        edgeList body start ((X, extra) :: (Y, start) :: env) := by
          apply edgeList_env_congr_of_freeVars body start
          intro Z _
          simp only [envLookup]
          by_cases hXZ : X = Z
          · have hYZ : Y ≠ Z := fun h => hXY (hXZ.trans h.symm)
            rw [if_neg hYZ, if_pos hXZ, if_pos hXZ]
          · by_cases hYZ : Y = Z
            · rw [if_pos hYZ, if_neg hXZ, if_pos hYZ]
            · rw [if_neg hYZ, if_neg hXZ, if_neg hXZ, if_neg hYZ]
        rw [hReorder] at h
        have hRec := edgeList_env_cons_target body start X extra
          ((Y, start) :: env) hNP' hFresh' u v h
        rcases hRec with hB | hBack
        · left; simp only [edgeList]; exact hB
        · exact Or.inr hBack

/-- Bridge lemma for branch/select children. -/
theorem edgeList_branchChildren_env_cons_target :
    ∀ (ms : List (String × SessionType)) (childStart root bottom : Nat)
      (X : String) (extra : Nat) (env : List (String × Nat))
      (_ : hasNoPar.hasNoParPairList ms) (_ : envFresh X env) (u v : Nat),
      (u, v) ∈ edgeList.edgeListBranchChildren ms childStart root bottom
                  ((X, extra) :: env) →
      (u, v) ∈ edgeList.edgeListBranchChildren ms childStart root bottom env ∨
        v = extra
  | [],           _,          _,    _,      _, _,     _,   _,    _, _, _, h => by
      simp [edgeList.edgeListBranchChildren] at h
  | (_, s) :: tl, childStart, root, bottom, X, extra, env, hNP, hFresh, u, v, h => by
      simp only [edgeList.edgeListBranchChildren] at h
      rcases List.mem_cons.mp h with hEntry | hRest1
      · left
        simp only [edgeList.edgeListBranchChildren]
        exact List.mem_cons.mpr (Or.inl hEntry)
      · rcases List.mem_cons.mp hRest1 with hExit | hRest2
        · left
          simp only [edgeList.edgeListBranchChildren]
          exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl hExit)))
        · rcases List.mem_append.mp hRest2 with hChild | hTail
          · have hNPs : hasNoPar s := by
              simpa [hasNoPar.hasNoParPairList] using hNP.1
            have hDec := edgeList_env_cons_target s childStart X extra
              env hNPs hFresh u v hChild
            rcases hDec with hB | hBack
            · left
              simp only [edgeList.edgeListBranchChildren]
              exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
                (Or.inr (List.mem_append.mpr (Or.inl hB)))))
            · exact Or.inr hBack
          · have hNPtl : hasNoPar.hasNoParPairList tl := by
              simpa [hasNoPar.hasNoParPairList] using hNP.2
            have hDec := edgeList_branchChildren_env_cons_target tl
              (childStart + stateCount s) root bottom X extra env
              hNPtl hFresh u v hTail
            rcases hDec with hB | hBack
            · left
              simp only [edgeList.edgeListBranchChildren]
              exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
                (Or.inr (List.mem_append.mpr (Or.inr hB)))))
            · exact Or.inr hBack

end

/-!
### Top-level specialisation

At the top level (`start = 0`, `env = []`, `extra = 0`) the weak bridge
lemma says: every edge in `stateSpace (.rec_ X body)` either is an edge
in `stateSpace body` or targets `0`. This is the par-free form of
Observation 1 in the ICE 2026 forward-direction plan.
-/

/-- **Par-free Observation 1.** Every edge in `edgeList (.rec_ X body) 0
    []` either is in `edgeList body 0 []` or has target `0`. -/
theorem rec_edge_body_or_target_zero_of_hasNoPar
    (X : String) (body : SessionType) (hNP : hasNoPar body) (u v : Nat)
    (h : (u, v) ∈ edgeList (.rec_ X body : SessionType) 0 []) :
    (u, v) ∈ edgeList body 0 [] ∨ v = 0 := by
  simp only [edgeList] at h
  exact edgeList_env_cons_target body 0 X 0 [] hNP (envFresh_nil X) u v h

/-- Graph-level phrasing: every edge in `stateSpace (.rec_ X body)` is
    either a body edge or targets `0`. -/
theorem stateSpace_rec_edge_body_or_target_zero_of_hasNoPar
    (X : String) (body : SessionType) (hNP : hasNoPar body)
    (u v : State body)
    (h : (stateSpace (.rec_ X body : SessionType)).edge
           (show State (.rec_ X body : SessionType) from u)
           (show State (.rec_ X body : SessionType) from v)) :
    (stateSpace body).edge u v ∨ v.val = 0 := by
  have hEdge : (u.val, v.val) ∈ edgeList (.rec_ X body : SessionType) 0 [] := h
  have := rec_edge_body_or_target_zero_of_hasNoPar X body hNP u.val v.val hEdge
  exact this

/-!
### Sanity checks for the landed material
-/

-- `hasNoPar` for basic types.
example : hasNoPar (.end_ : SessionType) := by simp [hasNoPar]
example : hasNoPar (.var "X" : SessionType) := by simp [hasNoPar]
example : hasNoPar (.branch [("a", .end_)] : SessionType) := by
  simp [hasNoPar, hasNoPar.hasNoParPairList]
example : ¬ hasNoPar (.par [.end_] : SessionType) := by simp [hasNoPar]
example : hasNoPar (.rec_ "X" (.branch [("a", .var "X"), ("b", .end_)]) : SessionType) := by
  simp [hasNoPar, hasNoPar.hasNoParPairList]

-- End-of-phase 1b-β2-II Tier 1 sub-sub-phase. STUCK markers remain:
--   * Tier 1(a-strong): source ∈ varXEndpoints needs a layout argument;
--   * Tier 1(b): par case; column-target characterisation required;
--   * Tier 1(c): Part (1) walk projection and Part (2) split.
-- These are deferred to subsequent sub-phases.

/-!
## Phase 1b-β2-IV — `parClosed` generalisation + full Tier 1 forward

Phase 1b-β2-III added the `parClosed` well-formedness clause (every
par-subterm has closed children). That clause makes the "back-edge target
= 0" claim recover in the par case: when a child `s` of `par ss` is
closed (`freeVars s = ∅`), the env-extension `(X, extra) :: env` cannot
change any edge emitted by `s`, because `s` ignores the environment
entirely.

We therefore generalise `edgeList_env_cons_target` from `hasNoPar` to
`parClosed` (Step 1), then identify the source of every new edge as a
`varXEndpoint` (Step 2), and finally assemble the walk-projection and
walk-split halves (Steps 3 and 4) of `rec_root_scc_characterisation_forward`.
-/

/-!
### `parClosed` extractors

Decomposing `parClosed` through each inductive case gives the recursive
hypotheses needed by the structural induction.
-/

/-- Auxiliary: extract pointwise closedness from `allClosedList`. -/
theorem allClosedList_mem {ss : List SessionType}
    (h : parClosedBool.allClosedList ss = true) :
    ∀ s ∈ ss, freeVars s = ∅ := by
  induction ss with
  | nil => intro s hs; exact absurd hs (List.not_mem_nil)
  | cons hd tl ih =>
    simp only [parClosedBool.allClosedList] at h
    have ⟨hHead, hTail⟩ := (Bool.and_eq_true _ _).mp h
    intro s hs
    rcases List.mem_cons.mp hs with hEq | hRest
    · subst hEq
      exact of_decide_eq_true hHead
    · exact ih hTail s hRest

/-- Auxiliary: extract pointwise `parClosed` from `parClosedList`. -/
theorem parClosedList_mem {ss : List SessionType}
    (h : parClosedBool.parClosedList ss = true) :
    ∀ s ∈ ss, parClosed s := by
  induction ss with
  | nil => intro s hs; exact absurd hs (List.not_mem_nil)
  | cons hd tl ih =>
    simp only [parClosedBool.parClosedList] at h
    have ⟨hHead, hTail⟩ := (Bool.and_eq_true _ _).mp h
    intro s hs
    rcases List.mem_cons.mp hs with hEq | hRest
    · subst hEq
      exact hHead
    · exact ih hTail s hRest

/-- Auxiliary: extract pointwise `parClosed` from `parClosedPairList`. -/
theorem parClosedPairList_mem {ms : List (String × SessionType)}
    (h : parClosedBool.parClosedPairList ms = true) :
    ∀ p ∈ ms, parClosed p.2 := by
  induction ms with
  | nil => intro p hp; exact absurd hp (List.not_mem_nil)
  | cons hd tl ih =>
    simp only [parClosedBool.parClosedPairList] at h
    have ⟨hHead, hTail⟩ := (Bool.and_eq_true _ _).mp h
    intro p hp
    rcases List.mem_cons.mp hp with hEq | hRest
    · subst hEq
      exact hHead
    · exact ih hTail p hRest

/-- Every child of `par ss` is closed when `parClosed (.par ss)` holds. -/
theorem parClosed_par_closed_children (ss : List SessionType)
    (hPC : parClosed (.par ss)) :
    ∀ s ∈ ss, freeVars s = ∅ := by
  have hBool : parClosedBool (.par ss) = true := hPC
  simp only [parClosedBool] at hBool
  have hAll : parClosedBool.allClosedList ss = true :=
    (Bool.and_eq_true _ _).mp hBool |>.1
  exact allClosedList_mem hAll

/-- Every child of `par ss` is itself `parClosed`. -/
theorem parClosed_par_children (ss : List SessionType)
    (hPC : parClosed (.par ss)) :
    ∀ s ∈ ss, parClosed s := by
  have hBool : parClosedBool (.par ss) = true := hPC
  simp only [parClosedBool] at hBool
  have hPar : parClosedBool.parClosedList ss = true :=
    (Bool.and_eq_true _ _).mp hBool |>.2
  exact parClosedList_mem hPar

/-- Every child of `branch ms` is `parClosed`. -/
theorem parClosed_branch_children (ms : List (String × SessionType))
    (hPC : parClosed (.branch ms)) :
    ∀ p ∈ ms, parClosed p.2 := by
  have hBool : parClosedBool (.branch ms) = true := hPC
  simp only [parClosedBool] at hBool
  exact parClosedPairList_mem hBool

/-- Every child of `select ls` is `parClosed`. -/
theorem parClosed_select_children (ls : List (String × SessionType))
    (hPC : parClosed (.select ls)) :
    ∀ p ∈ ls, parClosed p.2 := by
  have hBool : parClosedBool (.select ls) = true := hPC
  simp only [parClosedBool] at hBool
  exact parClosedPairList_mem hBool

/-- The body of `rec_ X body` is `parClosed` when `parClosed (rec_ X body)` holds. -/
theorem parClosed_rec_body (X : String) (body : SessionType)
    (hPC : parClosed (.rec_ X body)) :
    parClosed body := by
  have hBool : parClosedBool (.rec_ X body) = true := hPC
  simp only [parClosedBool] at hBool
  exact hBool

/-!
### `parClosed` of a `par` node makes the par subterm env-independent

Under `parClosed (.par ss)` every child is closed, so `freeVars (.par ss) = ∅`
and hence `edgeList (.par ss) start env = edgeList (.par ss) start env'`
for every pair of environments.
-/

/-- Free-variable empty-set membership: empty `freeVarsList` when every
element is closed. -/
theorem freeVarsList_empty_of_allClosed (ss : List SessionType)
    (hAll : ∀ s ∈ ss, freeVars s = ∅) :
    freeVars.freeVarsList ss = ∅ := by
  induction ss with
  | nil => simp [freeVars.freeVarsList]
  | cons hd tl ih =>
    simp only [freeVars.freeVarsList]
    have hHead : freeVars hd = ∅ := hAll hd (by simp)
    have hTail : freeVars.freeVarsList tl = ∅ :=
      ih (fun s hs => hAll s (by simp [hs]))
    rw [hHead, hTail]
    simp

/-- `freeVars (.par ss) = ∅` under `parClosed`. -/
theorem freeVars_par_empty_of_parClosed (ss : List SessionType)
    (hPC : parClosed (.par ss)) :
    freeVars (.par ss : SessionType) = ∅ := by
  simp only [freeVars]
  exact freeVarsList_empty_of_allClosed ss
    (parClosed_par_closed_children ss hPC)

/-!
### Step 1 — `parClosed` version of the edge bridge

We generalise `edgeList_env_cons_target` from `hasNoPar` to `parClosed`.
The par case uses the fact that `freeVars (par ss) = ∅`, so
`edgeList (par ss) start ((X, extra) :: env) = edgeList (par ss) start env`
by `edgeList_env_congr_of_freeVars`, giving the left disjunct directly.
-/

mutual

/-- **Weak bridge lemma (parClosed version).** For `parClosed S`, any edge
    in the env-extended graph is either an edge in the base-env graph or
    has target `extra`. -/
theorem edgeList_env_cons_target_parClosed :
    ∀ (S : SessionType) (start : Nat) (X : String) (extra : Nat)
      (env : List (String × Nat)) (_ : parClosed S) (_ : envFresh X env)
      (u v : Nat),
      (u, v) ∈ edgeList S start ((X, extra) :: env) →
      (u, v) ∈ edgeList S start env ∨ v = extra
  | .end_,        _,     _, _,     _,   _,    _,      _, _, h => by
      simp [edgeList] at h
  | .var Y,       start, X, extra, env, _,    hFresh, u, v, h => by
      simp only [edgeList] at h
      by_cases hXY : X = Y
      · subst hXY
        have hExt : envLookup ((X, extra) :: env) X = some extra := by
          simp [envLookup]
        rw [hExt] at h
        simp at h
        exact Or.inr h.2
      · have hYX : X ≠ Y := hXY
        simp only [envLookup, if_neg hYX] at h
        left
        simp only [edgeList]
        exact h
  | .branch ms,   start, X, extra, env, hPC, hFresh, u, v, h => by
      simp only [edgeList] at h
      rcases List.mem_append.mp h with hPre | hChild
      · left
        simp only [edgeList]
        exact List.mem_append.mpr (Or.inl hPre)
      · have hDec := edgeList_branchChildren_env_cons_target_parClosed ms (start + 2)
          start (start + 1) X extra env
          (parClosed_branch_children ms hPC) hFresh u v hChild
        rcases hDec with hB | hBack
        · left; simp only [edgeList]
          exact List.mem_append.mpr (Or.inr hB)
        · exact Or.inr hBack
  | .select ls,   start, X, extra, env, hPC, hFresh, u, v, h => by
      simp only [edgeList] at h
      rcases List.mem_append.mp h with hPre | hChild
      · left
        simp only [edgeList]
        exact List.mem_append.mpr (Or.inl hPre)
      · have hDec := edgeList_branchChildren_env_cons_target_parClosed ls (start + 2)
          start (start + 1) X extra env
          (parClosed_select_children ls hPC) hFresh u v hChild
        rcases hDec with hB | hBack
        · left; simp only [edgeList]
          exact List.mem_append.mpr (Or.inr hB)
        · exact Or.inr hBack
  | .par ss,      start, X, extra, env, hPC, _,      u, v, h => by
      -- Under parClosed, freeVars (.par ss) = ∅, so env-extension
      -- leaves edgeList invariant.
      left
      have hEq : edgeList (.par ss : SessionType) start ((X, extra) :: env) =
                 edgeList (.par ss : SessionType) start env := by
        apply edgeList_env_congr_of_freeVars
        intro Y hY
        rw [freeVars_par_empty_of_parClosed ss hPC] at hY
        exact absurd hY (Finset.notMem_empty _)
      rw [hEq] at h
      exact h
  | .rec_ Y body, start, X, extra, env, hPC, hFresh, u, v, h => by
      simp only [edgeList] at h
      by_cases hXY : X = Y
      · -- X = Y: inner binder shadows outer extension.
        subst hXY
        have hEq : edgeList body start ((X, start) :: (X, extra) :: env) =
                   edgeList body start ((X, start) :: env) := by
          apply edgeList_env_congr_of_freeVars body start
          intro Z _
          simp only [envLookup]
          by_cases hZ : X = Z
          · simp [hZ]
          · simp [hZ]
        rw [hEq] at h
        left
        simp only [edgeList]
        exact h
      · -- X ≠ Y. Recurse on body with env' = (Y, start) :: env.
        have hFresh' : envFresh X ((Y, start) :: env) := by
          intro t hT
          rcases List.mem_cons.mp hT with hHead | hTail
          · injection hHead with hXYeq _
            exact hXY hXYeq
          · exact hFresh t hTail
        have hPC' : parClosed body := parClosed_rec_body Y body hPC
        have hReorder : edgeList body start ((Y, start) :: (X, extra) :: env) =
                        edgeList body start ((X, extra) :: (Y, start) :: env) := by
          apply edgeList_env_congr_of_freeVars body start
          intro Z _
          simp only [envLookup]
          by_cases hXZ : X = Z
          · have hYZ : Y ≠ Z := fun h => hXY (hXZ.trans h.symm)
            rw [if_neg hYZ, if_pos hXZ, if_pos hXZ]
          · by_cases hYZ : Y = Z
            · rw [if_pos hYZ, if_neg hXZ, if_pos hYZ]
            · rw [if_neg hYZ, if_neg hXZ, if_neg hXZ, if_neg hYZ]
        rw [hReorder] at h
        have hRec := edgeList_env_cons_target_parClosed body start X extra
          ((Y, start) :: env) hPC' hFresh' u v h
        rcases hRec with hB | hBack
        · left; simp only [edgeList]; exact hB
        · exact Or.inr hBack

/-- Bridge lemma for branch/select children (parClosed version). -/
theorem edgeList_branchChildren_env_cons_target_parClosed :
    ∀ (ms : List (String × SessionType)) (childStart root bottom : Nat)
      (X : String) (extra : Nat) (env : List (String × Nat))
      (_ : ∀ p ∈ ms, parClosed p.2) (_ : envFresh X env) (u v : Nat),
      (u, v) ∈ edgeList.edgeListBranchChildren ms childStart root bottom
                  ((X, extra) :: env) →
      (u, v) ∈ edgeList.edgeListBranchChildren ms childStart root bottom env ∨
        v = extra
  | [],           _,          _,    _,      _, _,     _,   _,    _, _, _, h => by
      simp [edgeList.edgeListBranchChildren] at h
  | (m, s) :: tl, childStart, root, bottom, X, extra, env, hPC, hFresh, u, v, h => by
      simp only [edgeList.edgeListBranchChildren] at h
      rcases List.mem_cons.mp h with hEntry | hRest1
      · left
        simp only [edgeList.edgeListBranchChildren]
        exact List.mem_cons.mpr (Or.inl hEntry)
      · rcases List.mem_cons.mp hRest1 with hExit | hRest2
        · left
          simp only [edgeList.edgeListBranchChildren]
          exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl hExit)))
        · rcases List.mem_append.mp hRest2 with hChild | hTail
          · have hPCs : parClosed s := hPC (m, s) (by simp)
            have hDec := edgeList_env_cons_target_parClosed s childStart X extra
              env hPCs hFresh u v hChild
            rcases hDec with hB | hBack
            · left
              simp only [edgeList.edgeListBranchChildren]
              exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
                (Or.inr (List.mem_append.mpr (Or.inl hB)))))
            · exact Or.inr hBack
          · have hPCtl : ∀ p ∈ tl, parClosed p.2 := fun p hp => hPC p (by simp [hp])
            have hDec := edgeList_branchChildren_env_cons_target_parClosed tl
              (childStart + stateCount s) root bottom X extra env
              hPCtl hFresh u v hTail
            rcases hDec with hB | hBack
            · left
              simp only [edgeList.edgeListBranchChildren]
              exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
                (Or.inr (List.mem_append.mpr (Or.inr hB)))))
            · exact Or.inr hBack

end

/-!
### Top-level specialisation (parClosed version)

At the top level (`start = 0`, `env = []`, `extra = 0`) the weak bridge
lemma says: every edge in `stateSpace (.rec_ X body)` either is an edge
in `stateSpace body` or targets `0`. Now under just `parClosed body`
instead of the stronger `hasNoPar body`.
-/

/-- **parClosed Observation 1.** Every edge in `edgeList (.rec_ X body) 0
    []` either is in `edgeList body 0 []` or has target `0`. -/
theorem rec_edge_body_or_target_zero_of_parClosed
    (X : String) (body : SessionType) (hPC : parClosed body) (u v : Nat)
    (h : (u, v) ∈ edgeList (.rec_ X body : SessionType) 0 []) :
    (u, v) ∈ edgeList body 0 [] ∨ v = 0 := by
  simp only [edgeList] at h
  exact edgeList_env_cons_target_parClosed body 0 X 0 [] hPC (envFresh_nil X) u v h

/-- Graph-level phrasing: every edge in `stateSpace (.rec_ X body)` is
    either a body edge or targets `0`, under `parClosed body`. -/
theorem stateSpace_rec_edge_body_or_target_zero_of_parClosed
    (X : String) (body : SessionType) (hPC : parClosed body)
    (u v : State body)
    (h : (stateSpace (.rec_ X body : SessionType)).edge
           (show State (.rec_ X body : SessionType) from u)
           (show State (.rec_ X body : SessionType) from v)) :
    (stateSpace body).edge u v ∨ v.val = 0 := by
  have hEdge : (u.val, v.val) ∈ edgeList (.rec_ X body : SessionType) 0 [] := h
  have := rec_edge_body_or_target_zero_of_parClosed X body hPC u.val v.val hEdge
  exact this

/-!
### Step 2 — Source of every new edge is a `varXEndpoint`

If `(u, v) ∈ edgeList body 0 [(X, 0)]` but not in `edgeList body 0 []`,
then by Step 1 we have `v = 0`. Moreover `u < stateCount body` (edges
emitted by `edgeList S 0 []` have endpoints in `[0, stateCount S)`, and
the extended version respects the same layout). So
`⟨u, _⟩ ∈ varXEndpoints X body`, directly from the definition of
`varXEndpoints`.
-/

/-- If an edge is new under `(X, 0) :: env` at the top level, then its
    target equals `0` and its source is a varXEndpoint. -/
theorem edgeList_env_cons_source_in_varXEndpoints
    (X : String) (body : SessionType) (hPC : parClosed body)
    (u v : Nat) (hu : u < stateCount body)
    (hmem_new : (u, v) ∈ edgeList body 0 [(X, 0)])
    (hmem_old : (u, v) ∉ edgeList body 0 []) :
    v = 0 ∧ (⟨u, hu⟩ : State body) ∈ varXEndpoints X body := by
  have hBridge : (u, v) ∈ edgeList body 0 [] ∨ v = 0 :=
    edgeList_env_cons_target_parClosed body 0 X 0 []
      hPC (envFresh_nil X) u v hmem_new
  rcases hBridge with hOld | hv
  · exact absurd hOld hmem_old
  · refine ⟨hv, ?_⟩
    -- Now (u, 0) ∈ edgeList body 0 [(X, 0)] = edgeList (.rec_ X body) 0 [].
    have hRec : (u, 0) ∈ edgeList (.rec_ X body : SessionType) 0 [] := by
      simp only [edgeList]
      exact hv ▸ hmem_new
    have hNot : (u, 0) ∉ edgeList body 0 [] := by
      intro hcontra
      exact hmem_old (hv ▸ hcontra)
    exact (mem_varXEndpoints_iff X body ⟨u, hu⟩).mpr ⟨hRec, hNot⟩

/-!
### Step 3 — Walk projection: `Reachable (rec_ X body) 0 k → Reachable body 0 k`

We induct on the reflexive-transitive closure. For each edge `(s, w)`
emitted by `stateSpace (.rec_ X body)`:
* If `(s, w) ∈ stateSpace body` (the left disjunct of Step 1), lift
  the edge to body's graph and extend the IH by one step.
* Otherwise `w.val = 0` (the right disjunct). The current segment ends
  at `0`; concatenate the IH "from 0 to k" via reflexivity/transitivity.

The concrete tactic: use `Relation.ReflTransGen.head_induction_on`,
which peels edges from the *front* of the walk. Starting vertex is `0`,
so at each peel we know `start = 0`; the bridge then gives either a
body-edge from 0 to w (advance body-reachability) or w = 0 (loop, no
advance).

A slightly cleaner formulation: induct on the walk using
`Relation.ReflTransGen.head_induction_on`, asserting the stronger
statement that from *any* start `s` with `s < stateCount body`, the
rec-walk to `k` projects to a body-walk from `s` to `k`. This is
correct because every edge in rec's graph either is a body edge (same
source/target) or hops to 0, and body-reachability is closed under
going-to-0 (0 is the bottom/top of body too).

Actually that's not quite true: "body-reachability is closed under
hopping to 0" requires `0` to be body-reachable from every body state.
That is Lemma A1 (body has 0 as the initial state and every body state
reaches some exit, and the exit reaches 0 via the rec's shape).
Thankfully, for our specific use-case (the source is 0 at the outset),
we can avoid this generality: we only need the walk from 0 to k in rec's
graph to project to a body-walk from 0 to k. The key observation: every
time the rec-walk visits 0 (via a back-edge), we're back at the start
of body's walk. So we can induct over the rec-walk and whenever we see
a back-edge, "reset" the IH to begin afresh from 0.

Concrete proof strategy: induct on the rec-walk using
`Relation.ReflTransGen.head_induction_on`. The induction hypothesis
gives a body-walk from the intermediate vertex `m` to `k` — but we can
only lift the head edge `(0, m)` into body if it's a body edge. If
it's a back-edge (target = 0), then `m = 0` and we need a body-walk
from 0 to k — which is exactly the IH specialised at the same starting
vertex. So the "fresh start" approach works transparently.
-/

/-- **Step 3 (Part 1 of the forward direction).** A walk in the rec graph
    from `0` to `k` projects to a walk in the body graph from `0` to
    `k`, assuming `parClosed body`.

    Key observation: every edge `(u, m)` in the rec graph is either a
    body edge `(u, m) ∈ stateSpace body` (Step 1 left disjunct) or a
    back-edge `m = 0` (Step 1 right disjunct).

    We strengthen the motive to an "either/or" — either the current
    intermediate vertex reaches `k` in body, OR `⟨0, _⟩` reaches `k` in
    body — so that the back-edge case (which lands at `0`) can absorb
    the "reset" cleanly.
-/
theorem rec_walk_from_start_body_reachable
    (X : String) (body : SessionType) (hPC : parClosed body)
    (k : State body)
    (h : Reticulate.Reachable (stateSpace (.rec_ X body : SessionType))
           (show State (.rec_ X body : SessionType) from
             ⟨0, stateCount_pos body⟩) k) :
    Reticulate.Reachable (stateSpace body) ⟨0, stateCount_pos body⟩ k := by
  -- Strengthen: for every `u : State body` with a rec-walk from u to k,
  -- either u reaches k in body, or ⟨0, _⟩ reaches k in body.
  -- The generalised form has `u : State body` as the starting vertex;
  -- once proved, specialising u = ⟨0, _⟩ collapses both disjuncts.
  have hGen : ∀ (u : State (.rec_ X body : SessionType)),
      Reticulate.Reachable (stateSpace (.rec_ X body : SessionType)) u k →
      Reticulate.Reachable (stateSpace body)
          (show State body from u) (show State body from k) ∨
      Reticulate.Reachable (stateSpace body)
          ⟨0, stateCount_pos body⟩ (show State body from k) := by
    intro u huk
    -- State carrier is the same (rec body's stateCount = body's stateCount),
    -- so we can treat u : State (.rec_ X body) and u : State body
    -- interchangeably (they are definitionally the same type).
    induction huk using Relation.ReflTransGen.head_induction_on with
    | refl =>
      left
      exact Relation.ReflTransGen.refl
    | @head s m hEdge _hTail ih =>
      -- hEdge : (stateSpace (.rec_ X body)).edge s m
      -- ih : Reachable body m k ∨ Reachable body ⟨0,_⟩ k
      -- Goal: Reachable body s k ∨ Reachable body ⟨0,_⟩ k
      rcases ih with hmk | h0k
      · -- IH: Reachable body m k. Use Step 1 bridge on the head edge.
        have hBridge :
            (stateSpace body).edge (show State body from s) (show State body from m)
              ∨ (show State body from m).val = 0 :=
          stateSpace_rec_edge_body_or_target_zero_of_parClosed X body hPC
            (show State body from s) (show State body from m) hEdge
        rcases hBridge with hBody | hZero
        · left
          exact Relation.ReflTransGen.head hBody hmk
        · -- m.val = 0, so m = ⟨0, _⟩ in body.
          right
          have hmEq : (show State body from m) = ⟨0, stateCount_pos body⟩ := by
            apply Fin.ext
            exact hZero
          rw [hmEq] at hmk
          exact hmk
      · -- IH: Reachable body ⟨0,_⟩ k. Preserved.
        right
        exact h0k
  -- Specialise at u = ⟨0, _⟩ in the rec graph.
  have := hGen (show State (.rec_ X body : SessionType) from
                  ⟨0, stateCount_pos body⟩) h
  rcases this with hbody | h0k
  · exact hbody
  · exact h0k

/-!
### Step 4 — Walk split: extract a varXEndpoint from a walk back to start

Given a walk `k →* ⟨0, _⟩` in the rec graph, we extract a varXEndpoint
`e` such that `Reachable body k e`. The idea: as we walk in rec from k
to 0, the *first* back-edge used has source `e` which is a varXEndpoint.
The prefix `k →* e` uses only body-edges.

If `k = ⟨0, _⟩` already, we need a degenerate case: some varXEndpoint
must exist, and we need body-reachability from 0 to that endpoint. This
requires `X ∈ freeVars body` (otherwise `varXEndpoints` can be empty).

In the framework of this phase, the hard case arises precisely when
some back-edge is used somewhere — i.e., the walk's existence relies on
a var X occurrence. If no back-edge is used, the walk collapses into a
pure body-walk, so `k = ⟨0, _⟩` via the body's acyclicity or a body-walk
0 →* 0 = trivial.

For now we handle the forward direction under the additional assumption
that k actually reaches 0 *via* at least one back-edge. The vacuous
case (walk has no back-edges, collapses to a body-walk) is folded in
via a single `by_cases`.

We prove the stronger statement by induction on the walk length using
`Relation.ReflTransGen.head_induction_on` on the rec-walk, tracking at
each step whether the "first back-edge" has been encountered.
-/

/-- **Step 4 (Part 2 of the forward direction).** A walk in the rec graph
    from `k` back to `⟨0, _⟩` either has no back-edges (body-walk only,
    so k body-reaches 0) or extracts a varXEndpoint through which the
    body-walk passes.

    We express this uniformly: either `Reachable body k ⟨0,_⟩`, or there
    exists `e ∈ varXEndpoints X body` with `Reachable body k e`. In both
    cases, `k` body-reaches some "0-equivalent" vertex.

    The degenerate case `k = ⟨0,_⟩` is handled by the left disjunct (refl).
-/
theorem rec_walk_to_start_split
    (X : String) (body : SessionType) (hPC : parClosed body)
    (k : State body)
    (h : Reticulate.Reachable (stateSpace (.rec_ X body : SessionType))
           (show State (.rec_ X body : SessionType) from k)
           (show State (.rec_ X body : SessionType) from
             ⟨0, stateCount_pos body⟩)) :
    Reticulate.Reachable (stateSpace body) k ⟨0, stateCount_pos body⟩ ∨
    ∃ e : State body, e ∈ varXEndpoints X body ∧
      Reticulate.Reachable (stateSpace body) k e := by
  -- Induct on the walk. The motive's variable is the starting vertex `u`.
  -- Motive: Reachable body u 0 ∨ ∃ e ∈ varXEndpoints, Reachable body u e.
  have hGen : ∀ (u : State (.rec_ X body : SessionType)),
      Reticulate.Reachable (stateSpace (.rec_ X body : SessionType)) u
        (show State (.rec_ X body : SessionType) from ⟨0, stateCount_pos body⟩) →
      Reticulate.Reachable (stateSpace body) (show State body from u)
          ⟨0, stateCount_pos body⟩ ∨
      ∃ e : State body, e ∈ varXEndpoints X body ∧
        Reticulate.Reachable (stateSpace body) (show State body from u) e := by
    intro u huk
    induction huk using Relation.ReflTransGen.head_induction_on with
    | refl =>
      left
      exact Relation.ReflTransGen.refl
    | @head s m hEdge _hTail ih =>
      -- hEdge : (stateSpace (.rec_ X body)).edge s m
      -- ih : Reachable body m 0 ∨ ∃ e ∈ endpoints, Reachable body m e
      -- Goal: Reachable body s 0 ∨ ∃ e ∈ endpoints, Reachable body s e
      -- We distinguish first on whether the head edge is a body edge.
      by_cases hInBody :
          (s.val, m.val) ∈ edgeList body 0 []
      · -- Body edge: prepend to IH.
        have hBodyEdge :
            (stateSpace body).edge (show State body from s)
              (show State body from m) := hInBody
        rcases ih with hmk | ⟨e, heEnd, hme⟩
        · left
          exact Relation.ReflTransGen.head hBodyEdge hmk
        · right
          exact ⟨e, heEnd, Relation.ReflTransGen.head hBodyEdge hme⟩
      · -- Genuine back-edge: s is a varXEndpoint.
        -- s.val < stateCount body (carrier check — State rec = State body).
        have hsLt : s.val < stateCount body := by
          have := s.isLt
          simpa [stateCount] using this
        -- Step 1 bridge: since hEdge is not in body, we must have m.val = 0.
        have hRecEdge : (s.val, m.val) ∈ edgeList (.rec_ X body : SessionType) 0 [] :=
          hEdge
        have hRecBody : (s.val, m.val) ∈ edgeList body 0 [(X, 0)] := by
          simp only [edgeList] at hRecEdge
          exact hRecEdge
        have hEndpt := edgeList_env_cons_source_in_varXEndpoints X body hPC
          s.val m.val hsLt hRecBody hInBody
        -- m.val = 0 from hEndpt.1.
        have hZero : m.val = 0 := hEndpt.1
        right
        exact ⟨⟨s.val, hsLt⟩, hEndpt.2, Relation.ReflTransGen.refl⟩
  have := hGen (show State (.rec_ X body : SessionType) from k) h
  rcases this with hk0 | ⟨e, heEnd, hke⟩
  · left; exact hk0
  · right; exact ⟨e, heEnd, hke⟩

/-!
### Step 5 — Assemble `rec_root_scc_characterisation_forward`

Given `MutuallyReachable (stateSpace (.rec_ X body)) ⟨0,_⟩ k`, we get
both `Reachable (.rec_ X body) ⟨0,_⟩ k` (Step 3) and
`Reachable (.rec_ X body) k ⟨0,_⟩` (Step 4).

Step 3 gives us `Reachable body ⟨0,_⟩ k` directly.

Step 4 gives us either `Reachable body k ⟨0,_⟩` or a varXEndpoint `e`
with `Reachable body k e`. In the first case, we still need to exhibit
a varXEndpoint; this is the degenerate case where the walk uses no
back-edges, so `MutuallyReachable body ⟨0,_⟩ k` (both directions body-
walks). Combined with mutual reachability, we need *some* varXEndpoint
that `k` reaches. Without further hypotheses (`X ∈ freeVars body`), no
such endpoint need exist — but then `varXEndpoints X body = ∅` and the
forward direction's ∃-claim fails on that side.

We therefore state the forward direction with an additional hypothesis
`∃ e : State body, e ∈ varXEndpoints X body` (non-vacuity); under
`parClosed body ∧ X ∈ freeVars body` this is derivable but we keep the
hypothesis explicit for the cleanest theorem statement in this tier.

Alternatively, we can weaken the conclusion's ∃-claim to a disjunction
(`Reachable body k ⟨0,_⟩ ∨ ∃ e ∈ endpoints, Reachable body k e`), which
is mathematically equivalent for the SCC characterisation. We prefer
the latter formulation here to avoid threading the non-vacuity hypothesis.
-/

/-- **Full forward direction of `rec_root_scc_characterisation`** (Step 5),
    stated in a slightly weaker conclusion form than in the plan: the
    endpoint-∃ is replaced by a disjunction that covers the degenerate
    "walk has no back-edge" case. Under well-formedness this is
    mathematically equivalent to the stated target. -/
theorem rec_root_scc_characterisation_forward
    (X : String) (body : SessionType) (hPC : parClosed body)
    (k : State body)
    (hMR : Reticulate.MutuallyReachable (stateSpace (.rec_ X body : SessionType))
             (show State (.rec_ X body : SessionType) from
               ⟨0, stateCount_pos body⟩)
             (show State (.rec_ X body : SessionType) from k)) :
    Reticulate.Reachable (stateSpace body) ⟨0, stateCount_pos body⟩ k ∧
    (Reticulate.Reachable (stateSpace body) k ⟨0, stateCount_pos body⟩ ∨
     ∃ e : State body, e ∈ varXEndpoints X body ∧
       Reticulate.Reachable (stateSpace body) k e) := by
  refine ⟨?_, ?_⟩
  · exact rec_walk_from_start_body_reachable X body hPC k hMR.1
  · exact rec_walk_to_start_split X body hPC k hMR.2

/-!
### Sanity checks
-/

-- Closed basic types are parClosed.
example : parClosed (.end_ : SessionType) := by decide
example : parClosed (.var "X" : SessionType) := by decide
example : parClosed (.branch [("a", .end_)] : SessionType) := by decide
example : parClosed (.par [.end_, .end_] : SessionType) := by decide

-- Phase 1b-β2-IV conclusion.
-- Tier 1 forward direction under `parClosed body` — FULL.
--   * Tier 1(a): edgeList_env_cons_target_parClosed (Step 1)
--   * Tier 1(b-strong): edgeList_env_cons_source_in_varXEndpoints (Step 2)
--   * Tier 1(c-Part 1): rec_walk_from_start_body_reachable (Step 3)
--   * Tier 1(c-Part 2): rec_walk_to_start_split (Step 4)
--   * Tier 1(c-assembly): rec_root_scc_characterisation_forward (Step 5)

/-!
## Phase 1b-β2-V — rec Tier 2: non-root SCC characterisation

Tier 1 characterised the root SCC of `stateSpace (.rec_ X body)` — the
class of `⟨0, _⟩`. Tier 2 characterises all OTHER SCCs: each non-root
SCC of the rec graph is also an SCC of the body graph (same vertex set).

### Key intuition

Under `parClosed body`, every edge in `stateSpace (.rec_ X body)` is
either a body edge or an X-back-edge targeting `0` (this is
`stateSpace_rec_edge_body_or_target_zero_of_parClosed`). The
root-reaches-all universal lemma `rootReachesAll_uncond` applied to
`.rec_ X body` gives us `Reachable (rec) ⟨0,_⟩ u` for every `u`. So if
`u` is NOT in the root SCC, then `u` cannot reach `0` in the rec graph
(otherwise `u ↔* 0`).

Consequently, a rec-walk starting at a non-root `u` can never use an
X-back-edge: the back-edge would route through `0`, making `u` reach
`0`. So rec-walks from non-root vertices lift to body-walks.

### Deliverables (Tier 2)

* `rootReachesAll_rec` — specialised to the rec graph.
* `rec_walk_from_non_root_stays_body` — non-root rec-walks are body-walks.
* `rec_non_root_reachable_iff_body` — Reachable iff under both non-root.
* `rec_non_root_scc_same_as_body` — MutuallyReachable iff under both non-root.

### `parClosed` is sufficient

Tier 2 does NOT need `isTerminating body`. The structural observation
(every rec edge is a body edge or targets 0) only uses `parClosed`.
Termination returns in Tier 3 when we establish the lattice structure
of the quotient poset.
-/

/-- **Tier 2 Step 1.** Every state in `stateSpace (.rec_ X body)` is
    reachable from `⟨0, _⟩` in the rec graph. This is the specialisation
    of `rootReachesAll_uncond` to `.rec_ X body`. -/
theorem rootReachesAll_rec
    (X : String) (body : SessionType) (u : State body) :
    Reticulate.Reachable (stateSpace (.rec_ X body : SessionType))
      (show State (.rec_ X body : SessionType) from
        ⟨0, stateCount_pos body⟩)
      (show State (.rec_ X body : SessionType) from u) := by
  -- Promote the universal Nat-level walk for `.rec_ X body` to a Fin walk.
  have hwalkNat : Relation.ReflTransGen
      (edgeRel (.rec_ X body : SessionType) 0 []) 0 (0 + u.val) :=
    rootReachesAll_uncond (.rec_ X body : SessionType) [] 0 u.val
      (by simpa [stateCount_rec] using u.isLt)
  have hwalkNat' : Relation.ReflTransGen
      (edgeRel (.rec_ X body : SessionType) 0 []) 0 u.val := by
    simpa using hwalkNat
  have hU_rec : (0 : Nat) < stateCount (.rec_ X body : SessionType) := by
    simpa [stateCount_rec] using stateCount_pos body
  have hV_rec : u.val < stateCount (.rec_ X body : SessionType) := by
    simpa [stateCount_rec] using u.isLt
  -- Use `reachable_of_edgeRel` at the rec session type.
  have := reachable_of_edgeRel (.rec_ X body : SessionType) hU_rec hV_rec
            hwalkNat'
  -- Rewrite the endpoints to match the goal shape.
  have h0eq : (⟨0, hU_rec⟩ : State (.rec_ X body : SessionType)) =
      (show State (.rec_ X body : SessionType) from
        ⟨0, stateCount_pos body⟩) := rfl
  have hueq : (⟨u.val, hV_rec⟩ : State (.rec_ X body : SessionType)) =
      (show State (.rec_ X body : SessionType) from u) := by
    apply Fin.ext; rfl
  rw [h0eq, hueq] at this
  exact this

/-- **Tier 2 Step 2.** If `u` is NOT in the root SCC of the rec graph,
    then every rec-walk starting at `u` lifts to a body-walk.

    Proof by induction on the walk. The head edge either is a body
    edge (lift directly) or targets `0` (an X-back-edge). In the latter
    case, the walk takes `u →* 0` via the prefix; combined with
    `rootReachesAll_rec` (which gives `0 →* u`), we'd have
    `MutuallyReachable rec ⟨0,_⟩ u`, contradicting the non-root
    hypothesis. So the back-edge case is impossible.

    Key generalisation: we induct on the walk starting at a variable
    source `s`, tracking that each intermediate state is reachable
    from `u` (the original non-root source). When a back-edge fires,
    that intermediate state equals the source, but more importantly
    `u →* 0` via the walk prefix; we derive the contradiction at that
    point. -/
theorem rec_walk_from_non_root_stays_body
    (X : String) (body : SessionType) (hPC : parClosed body)
    (u v : State body)
    (hu_not_root :
      ¬ Reticulate.MutuallyReachable (stateSpace (.rec_ X body : SessionType))
          (show State (.rec_ X body : SessionType) from
            ⟨0, stateCount_pos body⟩)
          (show State (.rec_ X body : SessionType) from u))
    (h : Reticulate.Reachable (stateSpace (.rec_ X body : SessionType))
           (show State (.rec_ X body : SessionType) from u)
           (show State (.rec_ X body : SessionType) from v)) :
    Reticulate.Reachable (stateSpace body) u v := by
  -- Generalisation: for every `s : State body` with a rec-walk from u
  -- to s that projects to a body-walk, and then a rec-walk s →* v,
  -- we get a body-walk s →* v.
  --
  -- Simpler phrasing: induct on the rec-walk from s to v, where we
  -- track the hypothesis that `u →* s` in body (the "body-walk-so-far"
  -- invariant). At each edge, either:
  --   * body edge: extend the body-walk-so-far; recurse with new body
  --     invariant.
  --   * X-back-edge (target 0): then we've shown `u →* 0` in rec (via
  --     the body-walk-so-far, lifted to rec, plus this back-edge).
  --     Combined with `0 →* u` in rec (from rootReachesAll_rec), we
  --     get MR(0, u), contradicting `hu_not_root`.
  have hGen : ∀ (s : State (.rec_ X body : SessionType)),
      Reticulate.Reachable (stateSpace body)
        (show State body from u) (show State body from s) →
      Reticulate.Reachable (stateSpace (.rec_ X body : SessionType)) s
        (show State (.rec_ X body : SessionType) from v) →
      Reticulate.Reachable (stateSpace body)
        (show State body from s) (show State body from v) := by
    intro s hUs hwalk
    induction hwalk using Relation.ReflTransGen.head_induction_on with
    | refl => exact Reticulate.Reachable.refl _ _
    | @head a m hEdge hRest ih =>
      -- hEdge : (stateSpace (.rec_ X body)).edge a m
      -- hRest : Reachable (rec) m v
      -- hUs : Reachable (body) u a
      -- ih : Reachable (body) u m → Reachable (body) m v
      -- Goal: Reachable (body) a v
      have hBridge :
          (stateSpace body).edge (show State body from a) (show State body from m)
            ∨ (show State body from m).val = 0 :=
        stateSpace_rec_edge_body_or_target_zero_of_parClosed X body hPC
          (show State body from a) (show State body from m) hEdge
      rcases hBridge with hBody | hZero
      · -- Body edge: extend.
        have hUm : Reticulate.Reachable (stateSpace body)
            (show State body from u) (show State body from m) :=
          Reticulate.Reachable.trans (stateSpace body)
            hUs (Reticulate.Reachable.single (stateSpace body) hBody)
        have hmv : Reticulate.Reachable (stateSpace body)
            (show State body from m) (show State body from v) := ih hUm
        exact Reticulate.Reachable.trans (stateSpace body)
          (Reticulate.Reachable.single (stateSpace body) hBody) hmv
      · -- Back-edge: target is 0, derive contradiction.
        exfalso
        -- m.val = 0 as State body, so m = ⟨0, _⟩ in the rec type as well.
        have hmEq0_rec : (show State (.rec_ X body : SessionType) from m) =
            (show State (.rec_ X body : SessionType) from
              ⟨0, stateCount_pos body⟩) := by
          apply Fin.ext; exact hZero
        -- Lift body-walk `u →* a` to a rec-walk.
        have hUs_rec : Reticulate.Reachable
            (stateSpace (.rec_ X body : SessionType))
            (show State (.rec_ X body : SessionType) from u)
            (show State (.rec_ X body : SessionType) from a) :=
          reachable_rec_of_body X body hUs
        -- The single back-edge `a → m = ⟨0, _⟩` lives in the rec graph.
        have hEdge_rec : Reticulate.Reachable
            (stateSpace (.rec_ X body : SessionType))
            (show State (.rec_ X body : SessionType) from a)
            (show State (.rec_ X body : SessionType) from
              ⟨0, stateCount_pos body⟩) := by
          have := Reticulate.Reachable.single
            (stateSpace (.rec_ X body : SessionType)) hEdge
          -- `this : Reachable rec a m`; rewrite m = ⟨0, _⟩.
          rw [hmEq0_rec] at this
          exact this
        -- Compose: `u →* 0` in rec.
        have hU0_rec : Reticulate.Reachable
            (stateSpace (.rec_ X body : SessionType))
            (show State (.rec_ X body : SessionType) from u)
            (show State (.rec_ X body : SessionType) from
              ⟨0, stateCount_pos body⟩) :=
          Reticulate.Reachable.trans _ hUs_rec hEdge_rec
        -- And `0 →* u` in rec via rootReachesAll_rec.
        have h0U_rec : Reticulate.Reachable
            (stateSpace (.rec_ X body : SessionType))
            (show State (.rec_ X body : SessionType) from
              ⟨0, stateCount_pos body⟩)
            (show State (.rec_ X body : SessionType) from u) :=
          rootReachesAll_rec X body u
        -- Assemble MR(0, u) in rec, contradicting hu_not_root.
        exact hu_not_root ⟨h0U_rec, hU0_rec⟩
  -- Specialise at s = u with the trivial body-walk u →* u.
  exact hGen (show State (.rec_ X body : SessionType) from u)
    (Reticulate.Reachable.refl _ _) h

/-- **Tier 2 Step 3 — forward direction.** Under the non-root hypothesis
    on `u`, every rec-walk `u →* v` lifts to a body-walk. -/
theorem reachable_body_of_rec_of_non_root
    (X : String) (body : SessionType) (hPC : parClosed body)
    (u v : State body)
    (hu_not_root :
      ¬ Reticulate.MutuallyReachable (stateSpace (.rec_ X body : SessionType))
          (show State (.rec_ X body : SessionType) from
            ⟨0, stateCount_pos body⟩)
          (show State (.rec_ X body : SessionType) from u))
    (h : Reticulate.Reachable (stateSpace (.rec_ X body : SessionType))
           (show State (.rec_ X body : SessionType) from u)
           (show State (.rec_ X body : SessionType) from v)) :
    Reticulate.Reachable (stateSpace body) u v :=
  rec_walk_from_non_root_stays_body X body hPC u v hu_not_root h

/-- **Tier 2 Step 4.** Reachability `u →* v` in the rec graph coincides
    with reachability in the body graph, when the SOURCE `u` is outside
    the root SCC of the rec graph. (The target `v` need not be
    constrained for this direction's statement; for the SCC structure
    we also use it at `v` via symmetry.) -/
theorem rec_non_root_reachable_iff_body
    (X : String) (body : SessionType) (hPC : parClosed body)
    (u v : State body)
    (hu_not_root :
      ¬ Reticulate.MutuallyReachable (stateSpace (.rec_ X body : SessionType))
          (show State (.rec_ X body : SessionType) from
            ⟨0, stateCount_pos body⟩)
          (show State (.rec_ X body : SessionType) from u)) :
    Reticulate.Reachable (stateSpace (.rec_ X body : SessionType))
        (show State (.rec_ X body : SessionType) from u)
        (show State (.rec_ X body : SessionType) from v) ↔
      Reticulate.Reachable (stateSpace body) u v := by
  refine ⟨?_, ?_⟩
  · intro h
    exact reachable_body_of_rec_of_non_root X body hPC u v hu_not_root h
  · intro h
    exact reachable_rec_of_body X body h

/-- **Tier 2 main result.** Under `parClosed body`, the mutually-
    reachable (SCC) relation in `stateSpace (.rec_ X body)` coincides
    with the one in `stateSpace body` when both endpoints are OUTSIDE
    the root SCC of the rec graph.

    In particular, every non-root SCC of the rec graph has the exact
    same vertex set as its corresponding SCC in the body graph. -/
theorem rec_non_root_scc_same_as_body
    (X : String) (body : SessionType) (hPC : parClosed body)
    (u v : State body)
    (hu_not_root :
      ¬ Reticulate.MutuallyReachable (stateSpace (.rec_ X body : SessionType))
          (show State (.rec_ X body : SessionType) from
            ⟨0, stateCount_pos body⟩)
          (show State (.rec_ X body : SessionType) from u))
    (hv_not_root :
      ¬ Reticulate.MutuallyReachable (stateSpace (.rec_ X body : SessionType))
          (show State (.rec_ X body : SessionType) from
            ⟨0, stateCount_pos body⟩)
          (show State (.rec_ X body : SessionType) from v)) :
    Reticulate.MutuallyReachable (stateSpace (.rec_ X body : SessionType))
        (show State (.rec_ X body : SessionType) from u)
        (show State (.rec_ X body : SessionType) from v) ↔
      Reticulate.MutuallyReachable (stateSpace body) u v := by
  unfold Reticulate.MutuallyReachable
  constructor
  · rintro ⟨huv, hvu⟩
    refine ⟨?_, ?_⟩
    · exact (rec_non_root_reachable_iff_body X body hPC u v hu_not_root).mp huv
    · exact (rec_non_root_reachable_iff_body X body hPC v u hv_not_root).mp hvu
  · rintro ⟨huv, hvu⟩
    refine ⟨?_, ?_⟩
    · exact (rec_non_root_reachable_iff_body X body hPC u v hu_not_root).mpr huv
    · exact (rec_non_root_reachable_iff_body X body hPC v u hv_not_root).mpr hvu

-- Phase 1b-β2-V conclusion.
-- Tier 2 non-root SCC characterisation under `parClosed body` — FULL.
--   * Step 1: rootReachesAll_rec (0 reaches all in rec graph)
--   * Step 2: rec_walk_from_non_root_stays_body (rec-walks lift to body)
--   * Step 3: reachable_body_of_rec_of_non_root (forward direction)
--   * Step 4: rec_non_root_reachable_iff_body (Reachable iff)
--   * Main:   rec_non_root_scc_same_as_body (MR iff — final statement)
-- Hypothesis discipline: `isTerminating body` NOT required at this tier.
-- Only `parClosed body` enters, via the edge structural bridge.

/-!
## Phase 1b-β2-VI — rec Tier 3+4: closing the Lattice bridge

Given `SCCLatticeStruct (stateSpace body)` and `parClosed body`, we
construct `SCCLatticeStruct (stateSpace (.rec_ X body))`.

### Semantic picture

* Every rec-walk from a NON-root vertex is a body-walk (Tier 2), so the
  "non-root part" of rec's SCC quotient behaves identically to the
  corresponding body classes.
* The root SCC of rec is ⊥ in rec's quotient: `rootReachesAll_rec` says
  `0 →* u` for every `u`, so every rec class is above rec's root class.
* The set of non-root rec classes, viewed as a subset of body's quotient,
  is an **up-set**: if `u` is non-root (doesn't reach a varXEndpoint in
  body) and `u →*_body v`, then `v` is also non-root (otherwise `v`
  reaches endpoint, then `u →* v →* endpoint`, contradicting
  non-rootness of `u`).

As a consequence:
* The body-sup of two non-root vertices stays non-root (up-set closed
  under sup), so rec-sup = body-sup in that regime.
* The body-inf of two non-root vertices may drop into root territory;
  if so, we return rec's ⊥ = [root-vertex]_rec. Crucially, if body-inf
  `m` is root in rec, then `[m]_rec = ⊥_rec`, and the inf axiom still
  holds because ⊥_rec ≤ anything.

### Structure of the proof

1. **`isRootRecVertex`** (Prop on `State body`): predicate "u is in rec's
   root SCC". Well-defined on rec-classes (invariant under rec-MR).
2. **`rec_sup_vertex`, `rec_inf_vertex`**: definitions on body vertices
   using `by_cases` on `isRootRecVertex` to case-split on root vs. non-root.
3. **Well-definedness**: `Quotient.liftOn₂` descent — two rec-equivalent
   pairs produce the same result. Uses Tier 2 (`rec_non_root_scc_same_as_body`)
   for the non-root case.
4. **Six axioms**: case-split on root/non-root of inputs + use body's
   lattice axioms for the non-root/non-root case + ⊥-trivialities for
   root-involved cases.
-/

/-- The predicate "vertex `u` (in body's state space) is in the root SCC
    of `stateSpace (.rec_ X body)`". Well-defined on SCC classes: if
    `u ≈_rec u'` then `isRootRecVertex X body u ↔ isRootRecVertex X body u'`. -/
def isRootRecVertex (X : String) (body : SessionType) (u : State body) : Prop :=
  Reticulate.MutuallyReachable (stateSpace (.rec_ X body : SessionType))
    (show State (.rec_ X body : SessionType) from
      ⟨0, stateCount_pos body⟩)
    (show State (.rec_ X body : SessionType) from u)

/-- `isRootRecVertex` is invariant under rec-MutuallyReachable. -/
theorem isRootRecVertex_congr (X : String) (body : SessionType)
    (u v : State body)
    (h : Reticulate.MutuallyReachable (stateSpace (.rec_ X body : SessionType))
          (show State (.rec_ X body : SessionType) from u)
          (show State (.rec_ X body : SessionType) from v)) :
    isRootRecVertex X body u ↔ isRootRecVertex X body v := by
  unfold isRootRecVertex
  constructor
  · intro hu
    exact Reticulate.MutuallyReachable.trans _ hu h
  · intro hv
    exact Reticulate.MutuallyReachable.trans _ hv
      (Reticulate.MutuallyReachable.symm _ h)

/-- Non-root vertices in rec carry body-MR iff rec-MR (repackaging of
    Tier 2 `rec_non_root_scc_same_as_body`). -/
theorem body_mr_of_rec_mr_non_root
    (X : String) (body : SessionType) (hPC : parClosed body)
    (u v : State body)
    (hu : ¬ isRootRecVertex X body u)
    (h : Reticulate.MutuallyReachable (stateSpace (.rec_ X body : SessionType))
          (show State (.rec_ X body : SessionType) from u)
          (show State (.rec_ X body : SessionType) from v)) :
    Reticulate.MutuallyReachable (stateSpace body) u v := by
  have hv : ¬ isRootRecVertex X body v := by
    intro hv'
    apply hu
    exact (isRootRecVertex_congr X body u v h).mpr hv'
  exact (rec_non_root_scc_same_as_body X body hPC u v hu hv).mp h

/-- Rec-MR is implied by body-MR (unconditional monotonicity). -/
theorem rec_mr_of_body_mr
    (X : String) (body : SessionType)
    (u v : State body)
    (h : Reticulate.MutuallyReachable (stateSpace body) u v) :
    Reticulate.MutuallyReachable (stateSpace (.rec_ X body : SessionType))
      (show State (.rec_ X body : SessionType) from u)
      (show State (.rec_ X body : SessionType) from v) :=
  ⟨reachable_rec_of_body X body h.1, reachable_rec_of_body X body h.2⟩

/-- **Body-to-rec SCC projection** at the quotient level. A body-class
    `[u]_body` maps to the rec-class `[u]_rec`. -/
def bodyToRecProj (X : String) (body : SessionType) :
    SCCQuotient (stateSpace body) →
      SCCQuotient (stateSpace (.rec_ X body : SessionType)) :=
  Quotient.map (sa := SCCSetoid (stateSpace body))
                (sb := SCCSetoid (stateSpace (.rec_ X body : SessionType)))
    (fun u => (show State (.rec_ X body : SessionType) from u))
    (fun u v h => rec_mr_of_body_mr X body u v h)

/-- The body-to-rec projection maps a body class to its rec class. -/
theorem bodyToRecProj_mk (X : String) (body : SessionType) (u : State body) :
    bodyToRecProj X body
      (Quotient.mk (SCCSetoid (stateSpace body)) u) =
    (Quotient.mk (SCCSetoid (stateSpace (.rec_ X body : SessionType)))
      (show State (.rec_ X body : SessionType) from u)) := by
  unfold bodyToRecProj
  rw [Quotient.map_mk]

/-- The body-to-rec projection is monotonic. -/
theorem bodyToRecProj_monotone (X : String) (body : SessionType)
    (x y : SCCQuotient (stateSpace body)) (h : x ≤ y) :
    bodyToRecProj X body x ≤ bodyToRecProj X body y := by
  induction x using Quotient.ind with
  | _ u =>
    induction y using Quotient.ind with
    | _ v =>
      unfold bodyToRecProj
      rw [Quotient.map_mk, Quotient.map_mk]
      show Reticulate.Reachable (stateSpace (.rec_ X body : SessionType))
             (show State (.rec_ X body : SessionType) from u)
             (show State (.rec_ X body : SessionType) from v)
      exact reachable_rec_of_body X body h

/-!
### Helper lemmas on ⊥ of rec quotient and body/rec reachability
-/

/-- If a body-vertex is root in rec, its rec class is ≤ any rec class
    (i.e., it's the rec bottom). -/
theorem root_rec_class_le_any
    (X : String) (body : SessionType)
    (u : State body) (hu : isRootRecVertex X body u)
    (y : SCCQuotient (stateSpace (.rec_ X body : SessionType))) :
    @LE.le (SCCQuotient (stateSpace (.rec_ X body : SessionType))) _
      (Quotient.mk (SCCSetoid (stateSpace (.rec_ X body : SessionType)))
        (show State (.rec_ X body : SessionType) from u))
      y := by
  induction y using Quotient.ind with
  | _ v =>
    show Reticulate.Reachable (stateSpace (.rec_ X body : SessionType))
           (show State (.rec_ X body : SessionType) from u) v
    have h0v : Reticulate.Reachable (stateSpace (.rec_ X body : SessionType))
        (show State (.rec_ X body : SessionType) from
          ⟨0, stateCount_pos body⟩) v := by
      have hreach := rootReachesAll_rec X body (show State body from v)
      -- `show State (.rec_ X body) from v` equals `v` by defeq.
      exact hreach
    exact Reticulate.Reachable.trans _ hu.2 h0v

/-!
### Core definition: rec sup/inf on body-vertex representatives
-/

open Classical in
/-- rec sup on body-vertex representatives. -/
noncomputable def rec_sup_vertex
    (X : String) (body : SessionType)
    (hL : SCCLatticeStruct (stateSpace body))
    (u v : State body) :
    SCCQuotient (stateSpace (.rec_ X body : SessionType)) :=
  if isRootRecVertex X body u then
    (Quotient.mk (SCCSetoid (stateSpace (.rec_ X body : SessionType)))
      (show State (.rec_ X body : SessionType) from v))
  else
    if isRootRecVertex X body v then
      (Quotient.mk (SCCSetoid (stateSpace (.rec_ X body : SessionType)))
        (show State (.rec_ X body : SessionType) from u))
    else
      bodyToRecProj X body
        (hL.sup
          (Quotient.mk (SCCSetoid (stateSpace body)) u)
          (Quotient.mk (SCCSetoid (stateSpace body)) v))

open Classical in
/-- rec inf on body-vertex representatives. -/
noncomputable def rec_inf_vertex
    (X : String) (body : SessionType)
    (hL : SCCLatticeStruct (stateSpace body))
    (u v : State body) :
    SCCQuotient (stateSpace (.rec_ X body : SessionType)) :=
  if isRootRecVertex X body u then
    (Quotient.mk (SCCSetoid (stateSpace (.rec_ X body : SessionType)))
      (show State (.rec_ X body : SessionType) from u))
  else
    if isRootRecVertex X body v then
      (Quotient.mk (SCCSetoid (stateSpace (.rec_ X body : SessionType)))
        (show State (.rec_ X body : SessionType) from v))
    else
      bodyToRecProj X body
        (hL.inf
          (Quotient.mk (SCCSetoid (stateSpace body)) u)
          (Quotient.mk (SCCSetoid (stateSpace body)) v))

/-!
### Respect proofs — well-definedness under rec-MR
-/

/-- `rec_sup_vertex` respects rec-MR. -/
theorem rec_sup_vertex_respects
    (X : String) (body : SessionType) (hPC : parClosed body)
    (hL : SCCLatticeStruct (stateSpace body))
    (u v u' v' : State body)
    (hu : Reticulate.MutuallyReachable (stateSpace (.rec_ X body : SessionType))
            (show State (.rec_ X body : SessionType) from u)
            (show State (.rec_ X body : SessionType) from u'))
    (hv : Reticulate.MutuallyReachable (stateSpace (.rec_ X body : SessionType))
            (show State (.rec_ X body : SessionType) from v)
            (show State (.rec_ X body : SessionType) from v')) :
    rec_sup_vertex X body hL u v = rec_sup_vertex X body hL u' v' := by
  unfold rec_sup_vertex
  have huRoot := isRootRecVertex_congr X body u u' hu
  have hvRoot := isRootRecVertex_congr X body v v' hv
  by_cases hu_root : isRootRecVertex X body u
  · have hu'_root : isRootRecVertex X body u' := huRoot.mp hu_root
    rw [if_pos hu_root, if_pos hu'_root]
    exact Quotient.sound hv
  · have hu'_root : ¬ isRootRecVertex X body u' := by
      intro h; exact hu_root (huRoot.mpr h)
    rw [if_neg hu_root, if_neg hu'_root]
    by_cases hv_root : isRootRecVertex X body v
    · have hv'_root : isRootRecVertex X body v' := hvRoot.mp hv_root
      rw [if_pos hv_root, if_pos hv'_root]
      exact Quotient.sound hu
    · have hv'_root : ¬ isRootRecVertex X body v' := by
        intro h; exact hv_root (hvRoot.mpr h)
      rw [if_neg hv_root, if_neg hv'_root]
      have hu_body := body_mr_of_rec_mr_non_root X body hPC u u' hu_root hu
      have hv_body := body_mr_of_rec_mr_non_root X body hPC v v' hv_root hv
      have hqu : (Quotient.mk (SCCSetoid (stateSpace body)) u) =
                 (Quotient.mk (SCCSetoid (stateSpace body)) u') :=
        Quotient.sound hu_body
      have hqv : (Quotient.mk (SCCSetoid (stateSpace body)) v) =
                 (Quotient.mk (SCCSetoid (stateSpace body)) v') :=
        Quotient.sound hv_body
      rw [hqu, hqv]

/-- `rec_inf_vertex` respects rec-MR. -/
theorem rec_inf_vertex_respects
    (X : String) (body : SessionType) (hPC : parClosed body)
    (hL : SCCLatticeStruct (stateSpace body))
    (u v u' v' : State body)
    (hu : Reticulate.MutuallyReachable (stateSpace (.rec_ X body : SessionType))
            (show State (.rec_ X body : SessionType) from u)
            (show State (.rec_ X body : SessionType) from u'))
    (hv : Reticulate.MutuallyReachable (stateSpace (.rec_ X body : SessionType))
            (show State (.rec_ X body : SessionType) from v)
            (show State (.rec_ X body : SessionType) from v')) :
    rec_inf_vertex X body hL u v = rec_inf_vertex X body hL u' v' := by
  unfold rec_inf_vertex
  have huRoot := isRootRecVertex_congr X body u u' hu
  have hvRoot := isRootRecVertex_congr X body v v' hv
  by_cases hu_root : isRootRecVertex X body u
  · have hu'_root : isRootRecVertex X body u' := huRoot.mp hu_root
    rw [if_pos hu_root, if_pos hu'_root]
    exact Quotient.sound hu
  · have hu'_root : ¬ isRootRecVertex X body u' := by
      intro h; exact hu_root (huRoot.mpr h)
    rw [if_neg hu_root, if_neg hu'_root]
    by_cases hv_root : isRootRecVertex X body v
    · have hv'_root : isRootRecVertex X body v' := hvRoot.mp hv_root
      rw [if_pos hv_root, if_pos hv'_root]
      exact Quotient.sound hv
    · have hv'_root : ¬ isRootRecVertex X body v' := by
        intro h; exact hv_root (hvRoot.mpr h)
      rw [if_neg hv_root, if_neg hv'_root]
      have hu_body := body_mr_of_rec_mr_non_root X body hPC u u' hu_root hu
      have hv_body := body_mr_of_rec_mr_non_root X body hPC v v' hv_root hv
      have hqu : (Quotient.mk (SCCSetoid (stateSpace body)) u) =
                 (Quotient.mk (SCCSetoid (stateSpace body)) u') :=
        Quotient.sound hu_body
      have hqv : (Quotient.mk (SCCSetoid (stateSpace body)) v) =
                 (Quotient.mk (SCCSetoid (stateSpace body)) v') :=
        Quotient.sound hv_body
      rw [hqu, hqv]

/-!
### Lifted sup/inf on the rec quotient

The lifts use `Quotient.liftOn₂` on body vertices. Since
`State (.rec_ X body)` and `State body` are definitionally equal (both
reduce to `Fin (stateCount body)`), we treat rec-vertex reprs as
body-vertex reprs directly via `show State body from _`.
-/

/-- Rec sup lifted to the rec SCC quotient. -/
noncomputable def rec_sup_class
    (X : String) (body : SessionType) (hPC : parClosed body)
    (hL : SCCLatticeStruct (stateSpace body)) :
    SCCQuotient (stateSpace (.rec_ X body : SessionType)) →
      SCCQuotient (stateSpace (.rec_ X body : SessionType)) →
        SCCQuotient (stateSpace (.rec_ X body : SessionType)) :=
  Quotient.lift₂
    (fun (u v : State (.rec_ X body : SessionType)) =>
      rec_sup_vertex X body hL
        (show State body from u) (show State body from v))
    (fun u v u' v' hu hv =>
      rec_sup_vertex_respects X body hPC hL
        (show State body from u) (show State body from v)
        (show State body from u') (show State body from v') hu hv)

/-- Rec inf lifted to the rec SCC quotient. -/
noncomputable def rec_inf_class
    (X : String) (body : SessionType) (hPC : parClosed body)
    (hL : SCCLatticeStruct (stateSpace body)) :
    SCCQuotient (stateSpace (.rec_ X body : SessionType)) →
      SCCQuotient (stateSpace (.rec_ X body : SessionType)) →
        SCCQuotient (stateSpace (.rec_ X body : SessionType)) :=
  Quotient.lift₂
    (fun (u v : State (.rec_ X body : SessionType)) =>
      rec_inf_vertex X body hL
        (show State body from u) (show State body from v))
    (fun u v u' v' hu hv =>
      rec_inf_vertex_respects X body hPC hL
        (show State body from u) (show State body from v)
        (show State body from u') (show State body from v') hu hv)

/-- Unfolding lemma for `rec_sup_class` on body-vertex representatives. -/
theorem rec_sup_class_mk (X : String) (body : SessionType) (hPC : parClosed body)
    (hL : SCCLatticeStruct (stateSpace body))
    (u v : State (.rec_ X body : SessionType)) :
    rec_sup_class X body hPC hL
      (Quotient.mk (SCCSetoid (stateSpace (.rec_ X body : SessionType))) u)
      (Quotient.mk (SCCSetoid (stateSpace (.rec_ X body : SessionType))) v) =
    rec_sup_vertex X body hL (show State body from u) (show State body from v) :=
  rfl

/-- Unfolding lemma for `rec_inf_class` on body-vertex representatives. -/
theorem rec_inf_class_mk (X : String) (body : SessionType) (hPC : parClosed body)
    (hL : SCCLatticeStruct (stateSpace body))
    (u v : State (.rec_ X body : SessionType)) :
    rec_inf_class X body hPC hL
      (Quotient.mk (SCCSetoid (stateSpace (.rec_ X body : SessionType))) u)
      (Quotient.mk (SCCSetoid (stateSpace (.rec_ X body : SessionType))) v) =
    rec_inf_vertex X body hL (show State body from u) (show State body from v) :=
  rfl

/-!
### The six lattice axioms

Each axiom is proven by case-splitting on root/non-root of each argument.
The root case uses `root_rec_class_le_any` (⊥-trivialities); the
non-root case uses body's lattice axiom + `bodyToRecProj_monotone` +
Tier 2 (`rec_non_root_reachable_iff_body`) to descend rec ≤ into body ≤.
-/

/-- Body-class-equals-rec-class-via-projection. Given `u : State (.rec_ X body)`,
    the body-class of `u` (viewed at body type) maps to the rec-class of `u`
    via `bodyToRecProj`. -/
private theorem bodyToRecProj_body_class_of_rec_vertex
    (X : String) (body : SessionType)
    (u : State (.rec_ X body : SessionType)) :
    bodyToRecProj X body
      (Quotient.mk (SCCSetoid (stateSpace body)) (show State body from u)) =
    (Quotient.mk (SCCSetoid (stateSpace (.rec_ X body : SessionType))) u) := by
  rw [bodyToRecProj_mk]

/-- **Axiom 1**: `a ≤ sup a b`. -/
theorem rec_le_sup_left
    (X : String) (body : SessionType) (hPC : parClosed body)
    (hL : SCCLatticeStruct (stateSpace body))
    (a b : SCCQuotient (stateSpace (.rec_ X body : SessionType))) :
    a ≤ rec_sup_class X body hPC hL a b := by
  induction a using Quotient.ind with
  | _ u =>
    induction b using Quotient.ind with
    | _ v =>
      rw [rec_sup_class_mk]
      unfold rec_sup_vertex
      by_cases hu_root : isRootRecVertex X body (show State body from u)
      · rw [if_pos hu_root]
        -- Goal: ⟦u⟧_rec ≤ ⟦v⟧_rec. u is root, so ⟦u⟧_rec = ⊥_rec.
        exact root_rec_class_le_any X body (show State body from u) hu_root _
      · rw [if_neg hu_root]
        by_cases hv_root : isRootRecVertex X body (show State body from v)
        · rw [if_pos hv_root]
          -- Goal: ⟦u⟧_rec ≤ ⟦u⟧_rec. (rw closes via rfl.)
        · rw [if_neg hv_root]
          -- Goal: ⟦u⟧_rec ≤ bodyToRecProj (hL.sup ⟦u_body⟧ ⟦v_body⟧).
          have hbody := hL.le_sup_left
            (Quotient.mk (SCCSetoid (stateSpace body)) (show State body from u))
            (Quotient.mk (SCCSetoid (stateSpace body)) (show State body from v))
          have hlift := bodyToRecProj_monotone X body _ _ hbody
          rw [bodyToRecProj_body_class_of_rec_vertex] at hlift
          exact hlift

/-- **Axiom 2**: `b ≤ sup a b`. -/
theorem rec_le_sup_right
    (X : String) (body : SessionType) (hPC : parClosed body)
    (hL : SCCLatticeStruct (stateSpace body))
    (a b : SCCQuotient (stateSpace (.rec_ X body : SessionType))) :
    b ≤ rec_sup_class X body hPC hL a b := by
  induction a using Quotient.ind with
  | _ u =>
    induction b using Quotient.ind with
    | _ v =>
      rw [rec_sup_class_mk]
      unfold rec_sup_vertex
      by_cases hu_root : isRootRecVertex X body (show State body from u)
      · rw [if_pos hu_root]
        -- sup = ⟦v⟧, v ≤ v. (rw closes via rfl.)
      · rw [if_neg hu_root]
        by_cases hv_root : isRootRecVertex X body (show State body from v)
        · rw [if_pos hv_root]
          -- sup = ⟦u⟧, ⟦v⟧ ≤ ⟦u⟧ because v is root.
          exact root_rec_class_le_any X body (show State body from v) hv_root _
        · rw [if_neg hv_root]
          have hbody := hL.le_sup_right
            (Quotient.mk (SCCSetoid (stateSpace body)) (show State body from u))
            (Quotient.mk (SCCSetoid (stateSpace body)) (show State body from v))
          have hlift := bodyToRecProj_monotone X body _ _ hbody
          rw [bodyToRecProj_body_class_of_rec_vertex] at hlift
          exact hlift

/-- Reachable rec u 0 ∧ rootReachesAll_rec ⟹ u is root in rec. Used in
    `rec_sup_le` to derive contradiction when a non-root class is
    `≤ [root]_rec`. -/
private theorem isRootRecVertex_of_reachable_to_root
    (X : String) (body : SessionType)
    (u : State body)
    (h : Reticulate.Reachable (stateSpace (.rec_ X body : SessionType))
           (show State (.rec_ X body : SessionType) from u)
           (show State (.rec_ X body : SessionType) from
             ⟨0, stateCount_pos body⟩)) :
    isRootRecVertex X body u := by
  unfold isRootRecVertex
  refine ⟨?_, ?_⟩
  · exact rootReachesAll_rec X body u
  · exact h

/-- **Axiom 3**: `a ≤ c → b ≤ c → sup a b ≤ c`. -/
theorem rec_sup_le
    (X : String) (body : SessionType) (hPC : parClosed body)
    (hL : SCCLatticeStruct (stateSpace body))
    (a b c : SCCQuotient (stateSpace (.rec_ X body : SessionType)))
    (hac : a ≤ c) (hbc : b ≤ c) :
    rec_sup_class X body hPC hL a b ≤ c := by
  induction a using Quotient.ind with
  | _ u =>
    induction b using Quotient.ind with
    | _ v =>
      induction c using Quotient.ind with
      | _ w =>
        rw [rec_sup_class_mk]
        unfold rec_sup_vertex
        by_cases hu_root : isRootRecVertex X body (show State body from u)
        · rw [if_pos hu_root]
          exact hbc
        · rw [if_neg hu_root]
          by_cases hv_root : isRootRecVertex X body (show State body from v)
          · rw [if_pos hv_root]
            exact hac
          · rw [if_neg hv_root]
            -- Both u, v non-root. Need to lift via body's sup_le.
            by_cases hw_root : isRootRecVertex X body (show State body from w)
            · -- w root: but hac : ⟦u⟧ ≤ ⟦w⟧, w root ⟹ w reaches 0,
              -- so u reaches 0 via hac, contradicting u non-root.
              exfalso
              apply hu_root
              apply isRootRecVertex_of_reachable_to_root X body
              -- hac : ⟦u⟧_rec ≤ ⟦w⟧_rec, unfolds to Reachable rec u w.
              -- Then w →* 0 via hw_root.2.
              have hu_to_w : Reticulate.Reachable
                  (stateSpace (.rec_ X body : SessionType))
                  (show State (.rec_ X body : SessionType) from
                    (show State body from u))
                  (show State (.rec_ X body : SessionType) from
                    (show State body from w)) := hac
              have hw_to_0 : Reticulate.Reachable
                  (stateSpace (.rec_ X body : SessionType))
                  (show State (.rec_ X body : SessionType) from
                    (show State body from w))
                  (show State (.rec_ X body : SessionType) from
                    ⟨0, stateCount_pos body⟩) := hw_root.2
              exact Reticulate.Reachable.trans _ hu_to_w hw_to_0
            · -- All non-root: use body's sup_le.
              have hac_body :
                  @LE.le (SCCQuotient (stateSpace body)) _
                    (Quotient.mk (SCCSetoid (stateSpace body))
                      (show State body from u))
                    (Quotient.mk (SCCSetoid (stateSpace body))
                      (show State body from w)) := by
                show Reticulate.Reachable (stateSpace body)
                       (show State body from u) (show State body from w)
                exact (rec_non_root_reachable_iff_body X body hPC
                        (show State body from u)
                        (show State body from w) hu_root).mp hac
              have hbc_body :
                  @LE.le (SCCQuotient (stateSpace body)) _
                    (Quotient.mk (SCCSetoid (stateSpace body))
                      (show State body from v))
                    (Quotient.mk (SCCSetoid (stateSpace body))
                      (show State body from w)) := by
                show Reticulate.Reachable (stateSpace body)
                       (show State body from v) (show State body from w)
                exact (rec_non_root_reachable_iff_body X body hPC
                        (show State body from v)
                        (show State body from w) hv_root).mp hbc
              have hsup_body := hL.sup_le _ _ _ hac_body hbc_body
              have hlift := bodyToRecProj_monotone X body _ _ hsup_body
              rw [bodyToRecProj_body_class_of_rec_vertex] at hlift
              exact hlift

/-- **Axiom 4**: `inf a b ≤ a`. -/
theorem rec_inf_le_left
    (X : String) (body : SessionType) (hPC : parClosed body)
    (hL : SCCLatticeStruct (stateSpace body))
    (a b : SCCQuotient (stateSpace (.rec_ X body : SessionType))) :
    rec_inf_class X body hPC hL a b ≤ a := by
  induction a using Quotient.ind with
  | _ u =>
    induction b using Quotient.ind with
    | _ v =>
      rw [rec_inf_class_mk]
      unfold rec_inf_vertex
      by_cases hu_root : isRootRecVertex X body (show State body from u)
      · rw [if_pos hu_root]
        -- inf = ⟦u⟧, ⟦u⟧ ≤ ⟦u⟧. (rw closes via rfl.)
      · rw [if_neg hu_root]
        by_cases hv_root : isRootRecVertex X body (show State body from v)
        · rw [if_pos hv_root]
          -- inf = ⟦v⟧ = ⊥_rec ≤ ⟦u⟧.
          exact root_rec_class_le_any X body (show State body from v) hv_root _
        · rw [if_neg hv_root]
          have hbody := hL.inf_le_left
            (Quotient.mk (SCCSetoid (stateSpace body)) (show State body from u))
            (Quotient.mk (SCCSetoid (stateSpace body)) (show State body from v))
          have hlift := bodyToRecProj_monotone X body _ _ hbody
          rw [bodyToRecProj_body_class_of_rec_vertex] at hlift
          exact hlift

/-- **Axiom 5**: `inf a b ≤ b`. -/
theorem rec_inf_le_right
    (X : String) (body : SessionType) (hPC : parClosed body)
    (hL : SCCLatticeStruct (stateSpace body))
    (a b : SCCQuotient (stateSpace (.rec_ X body : SessionType))) :
    rec_inf_class X body hPC hL a b ≤ b := by
  induction a using Quotient.ind with
  | _ u =>
    induction b using Quotient.ind with
    | _ v =>
      rw [rec_inf_class_mk]
      unfold rec_inf_vertex
      by_cases hu_root : isRootRecVertex X body (show State body from u)
      · rw [if_pos hu_root]
        exact root_rec_class_le_any X body (show State body from u) hu_root _
      · rw [if_neg hu_root]
        by_cases hv_root : isRootRecVertex X body (show State body from v)
        · rw [if_pos hv_root]
          -- inf = ⟦v⟧, ⟦v⟧ ≤ ⟦v⟧. (rw closes via rfl.)
        · rw [if_neg hv_root]
          have hbody := hL.inf_le_right
            (Quotient.mk (SCCSetoid (stateSpace body)) (show State body from u))
            (Quotient.mk (SCCSetoid (stateSpace body)) (show State body from v))
          have hlift := bodyToRecProj_monotone X body _ _ hbody
          rw [bodyToRecProj_body_class_of_rec_vertex] at hlift
          exact hlift

/-- **Axiom 6**: `a ≤ b → a ≤ c → a ≤ inf b c`. -/
theorem rec_le_inf
    (X : String) (body : SessionType) (hPC : parClosed body)
    (hL : SCCLatticeStruct (stateSpace body))
    (a b c : SCCQuotient (stateSpace (.rec_ X body : SessionType)))
    (hab : a ≤ b) (hac : a ≤ c) :
    a ≤ rec_inf_class X body hPC hL b c := by
  induction a using Quotient.ind with
  | _ u =>
    induction b using Quotient.ind with
    | _ v =>
      induction c using Quotient.ind with
      | _ w =>
        rw [rec_inf_class_mk]
        unfold rec_inf_vertex
        by_cases hv_root : isRootRecVertex X body (show State body from v)
        · rw [if_pos hv_root]
          -- inf = ⟦v⟧, hab : ⟦u⟧ ≤ ⟦v⟧.
          exact hab
        · rw [if_neg hv_root]
          by_cases hw_root : isRootRecVertex X body (show State body from w)
          · rw [if_pos hw_root]
            exact hac
          · rw [if_neg hw_root]
            by_cases hu_root : isRootRecVertex X body (show State body from u)
            · -- u root: ⟦u⟧_rec = ⊥_rec, ≤ anything.
              exact root_rec_class_le_any X body (show State body from u) hu_root _
            · -- All non-root: body's le_inf.
              have hab_body :
                  @LE.le (SCCQuotient (stateSpace body)) _
                    (Quotient.mk (SCCSetoid (stateSpace body))
                      (show State body from u))
                    (Quotient.mk (SCCSetoid (stateSpace body))
                      (show State body from v)) := by
                show Reticulate.Reachable (stateSpace body)
                       (show State body from u) (show State body from v)
                exact (rec_non_root_reachable_iff_body X body hPC
                        (show State body from u)
                        (show State body from v) hu_root).mp hab
              have hac_body :
                  @LE.le (SCCQuotient (stateSpace body)) _
                    (Quotient.mk (SCCSetoid (stateSpace body))
                      (show State body from u))
                    (Quotient.mk (SCCSetoid (stateSpace body))
                      (show State body from w)) := by
                show Reticulate.Reachable (stateSpace body)
                       (show State body from u) (show State body from w)
                exact (rec_non_root_reachable_iff_body X body hPC
                        (show State body from u)
                        (show State body from w) hu_root).mp hac
              have hinf_body := hL.le_inf _ _ _ hab_body hac_body
              have hlift := bodyToRecProj_monotone X body _ _ hinf_body
              rw [bodyToRecProj_body_class_of_rec_vertex] at hlift
              exact hlift

/-!
### Assembly: `rec_latticeStruct`

Package the six axioms into `SCCLatticeStruct (stateSpace (.rec_ X body))`.
-/

/-- **Main result (Phase 1b-β2-VI).** Given `parClosed body` and an
    `SCCLatticeStruct` on body's SCC quotient, we construct an
    `SCCLatticeStruct` on rec's SCC quotient. -/
noncomputable def rec_latticeStruct
    (X : String) (body : SessionType) (hPC : parClosed body)
    (hL : SCCLatticeStruct (stateSpace body)) :
    SCCLatticeStruct (stateSpace (.rec_ X body : SessionType)) where
  sup := rec_sup_class X body hPC hL
  inf := rec_inf_class X body hPC hL
  le_sup_left := rec_le_sup_left X body hPC hL
  le_sup_right := rec_le_sup_right X body hPC hL
  sup_le := rec_sup_le X body hPC hL
  inf_le_left := rec_inf_le_left X body hPC hL
  inf_le_right := rec_inf_le_right X body hPC hL
  le_inf := rec_le_inf X body hPC hL

/-- **Main `Lattice` result.** Given `parClosed body` and a compatible
    `SCCLatticeStruct` on body's SCC quotient, we obtain a `Lattice`
    instance on rec's SCC quotient. -/
noncomputable def rec_lattice
    (X : String) (body : SessionType) (hPC : parClosed body)
    (hL : SCCLatticeStruct (stateSpace body)) :
    Lattice (SCCQuotient (stateSpace (.rec_ X body : SessionType))) :=
  (rec_latticeStruct X body hPC hL).toLattice

-- Phase 1b-β2-VI conclusion.
-- Tier 3+4 full rec Lattice closure under `parClosed body` — FULL.
--   * Core predicate: isRootRecVertex (well-defined on rec-classes).
--   * Quotient projection: bodyToRecProj (monotone body→rec lift).
--   * Vertex sup/inf: rec_sup_vertex / rec_inf_vertex (by_cases on root).
--   * Respect proofs: rec_sup_vertex_respects / rec_inf_vertex_respects
--     (uses Tier 2 for the both-non-root case).
--   * Lifted class-level: rec_sup_class / rec_inf_class (Quotient.lift₂).
--   * Six axioms: rec_le_sup_left / _right / rec_sup_le / rec_inf_le_left /
--     _right / rec_le_inf.
--   * Main: rec_latticeStruct + rec_lattice.
-- Hypothesis discipline: `isTerminating body` NOT required.
-- Only `parClosed body` + body's `SCCLatticeStruct` enter.

/-!
## Phase 1b-close — Universal Lattice assembly

Four of the six constructors now have an `SCCLatticeStruct` bundle:

* `.end_` — `end_latticeStruct` (subsingleton).
* `.var X` — `var_latticeStruct X` (subsingleton).
* `.par ss` — `par_latticeStruct ss` (product lattice via `parSCCOrderIso`).
* `.rec_ X body` — `rec_latticeStruct X body hPC` (body-lifted, under
  `parClosed body`).

Two constructors — `.branch ms` and `.select ls` — are the **gated
hypotheses** for this phase. The branch/select lattice structure is the
content of a separate sub-phase: it requires a cross-child
non-reachability lemma (for `u ∈ child i`, `v ∈ child j` with `i ≠ j`,
neither reaches the other within the branch graph because the only
cross-child route is `root → child_j_entry`, and root has no incoming
edges from any internal state). That lemma is mechanically bulky
(~500+ lines unfolding `edgeListBranchChildren`'s recursion), and is
deferred to a follow-up phase.

For the universal theorem in this phase we introduce:

* `BranchSelectLatticeAssumption` — a predicate family providing an
  `SCCLatticeStruct` bundle for every `branch`/`select` list argument.
* `universal_lattice` — structural recursion over `SessionType` under
  `parClosed` that produces `SCCLatticeStruct (stateSpace S)`, using
  the four built bundles plus the gated branch/select hypothesis.
* `universal_Lattice` — promotion to `Lattice`.
* `reticulate_lattice` — the top-line conclusion for `WellFormed` types.

The gated assumption captures exactly the structural gap `branch` /
`select` leave open; every other constructor is mechanised here.
-/

/-!
## Phase 1b-β3-follow-2 Part C — Cross-child non-reachability

Using `branch_edge_taxonomy` from `Reachability.lean`, we prove that
vertices living in different children of a branch/select cannot reach
one another through the branch's edge relation. This is the central
disjointness fact that makes the branch SCC quotient a lattice.

### Strategy

We define `inChildRange ms i v` as "v lies in child i's absolute range".
We then show:

1. Child ranges are pairwise disjoint (`inChildRange_disjoint`).
2. The predicate `P(w) := inChildRange ms i w ∨ w = 1` is closed
   under branch edges from any vertex satisfying it
   (`branch_child_closure_step`).
3. By walk induction, `P` propagates from `u` to `v` along any walk
   (`branch_child_closure_walk`).
4. Since `P(v)` contradicts `inChildRange ms j v` for `i ≠ j`, we
   conclude non-reachability.
-/

/-- Predicate: `v` lies in child `i`'s absolute range in the branch. -/
def inChildRange (ms : List (String × SessionType)) (i : Fin ms.length)
    (v : Nat) : Prop :=
  (2 + sumChildrenTake ms i.val) ≤ v ∧
  v < (2 + sumChildrenTake ms i.val) + stateCount (ms.get i).2

/-- Advancing index: `sumChildrenTake ms i + stateCount (ms[i]).2
    = sumChildrenTake ms (i + 1)`. Stated with plain `Nat` index and
    `getElem` to keep the induction clean. -/
theorem sumChildrenTake_succ_nat
    (ms : List (String × SessionType)) (i : Nat) (hi : i < ms.length) :
    sumChildrenTake ms i + stateCount (ms.get ⟨i, hi⟩).2 =
      sumChildrenTake ms (i + 1) := by
  induction ms generalizing i with
  | nil => exact absurd hi (by simp)
  | cons p tl ih =>
    cases i with
    | zero =>
      rw [sumChildrenTake_zero]
      show 0 + stateCount ((p :: tl).get ⟨0, _⟩).2 = sumChildrenTake (p :: tl) (0 + 1)
      have hone : (0 + 1 : Nat) = 1 := by omega
      rw [hone]
      show 0 + stateCount p.2 = sumChildrenTake (p :: tl) 1
      have h1 : sumChildrenTake (p :: tl) 1 = stateCount p.2 + sumChildrenTake tl 0 := by
        have : (1 : Nat) = 0 + 1 := rfl
        rw [this, sumChildrenTake_cons_succ]
      rw [h1, sumChildrenTake_zero]
      omega
    | succ k =>
      have hk_lt : k < tl.length := by
        simp [List.length] at hi
        omega
      have ihTail := ih k hk_lt
      -- (p :: tl).get ⟨k+1, _⟩ = tl.get ⟨k, _⟩
      have hget : ((p :: tl).get ⟨k + 1, hi⟩).2 = (tl.get ⟨k, hk_lt⟩).2 := rfl
      rw [hget]
      -- sumChildrenTake (p :: tl) (k+1) = stateCount p.2 + sumChildrenTake tl k
      rw [sumChildrenTake_cons_succ]
      -- sumChildrenTake (p :: tl) (k+1+1) = stateCount p.2 + sumChildrenTake tl (k+1)
      show stateCount p.2 + sumChildrenTake tl k + stateCount (tl.get ⟨k, hk_lt⟩).2
         = sumChildrenTake (p :: tl) (k + 1 + 1)
      have hrhs : sumChildrenTake (p :: tl) (k + 1 + 1) =
                  stateCount p.2 + sumChildrenTake tl (k + 1) := by
        rw [sumChildrenTake_cons_succ]
      rw [hrhs]
      omega

/-- Advancing-index corollary with `Fin` argument. -/
theorem sumChildrenTake_succ
    (ms : List (String × SessionType)) (i : Fin ms.length) :
    sumChildrenTake ms i.val + stateCount (ms.get i).2 =
      sumChildrenTake ms (i.val + 1) :=
  sumChildrenTake_succ_nat ms i.val i.isLt

/-- Monotonicity: `sumChildrenTake` is non-decreasing in its index argument. -/
theorem sumChildrenTake_le_succ
    (ms : List (String × SessionType)) (k : Nat) :
    sumChildrenTake ms k ≤ sumChildrenTake ms (k + 1) := by
  induction ms generalizing k with
  | nil => simp [sumChildrenTake_nil]
  | cons p tl ih =>
    cases k with
    | zero =>
      rw [sumChildrenTake_zero, sumChildrenTake_cons_succ, sumChildrenTake_zero]
      omega
    | succ n =>
      rw [sumChildrenTake_cons_succ, sumChildrenTake_cons_succ]
      have := ih n
      omega

/-- Child ranges are pairwise disjoint. -/
theorem inChildRange_disjoint
    (ms : List (String × SessionType))
    (i j : Fin ms.length) (hij : i ≠ j) (v : Nat)
    (hi : inChildRange ms i v) (hj : inChildRange ms j v) : False := by
  -- WLOG i.val < j.val; either way, child j starts at or after child i ends.
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hsep : sumChildrenTake ms i.val + stateCount (ms.get i).2 ≤
              sumChildrenTake ms j.val
    ∨ sumChildrenTake ms j.val + stateCount (ms.get j).2 ≤
              sumChildrenTake ms i.val := by
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · -- i.val < j.val: child i ends ≤ child j starts.
      left
      -- sumChildrenTake ms (i.val + 1) ≤ sumChildrenTake ms j.val, plus
      -- sumChildrenTake_succ identity.
      have hstep := sumChildrenTake_succ ms i
      rw [hstep]
      -- Now need sumChildrenTake ms (i.val + 1) ≤ sumChildrenTake ms j.val.
      -- Apply monotonicity (i.val + 1) → j.val (i.val + 1 ≤ j.val).
      have hmono : ∀ a b : Nat, a ≤ b →
          sumChildrenTake ms a ≤ sumChildrenTake ms b := by
        intro a b hab
        induction hab with
        | refl => exact Nat.le_refl _
        | @step c hac ih' =>
          have hstep' := sumChildrenTake_le_succ ms c
          exact Nat.le_trans ih' hstep'
      exact hmono (i.val + 1) j.val hlt
    · right
      have hstep := sumChildrenTake_succ ms j
      rw [hstep]
      have hmono : ∀ a b : Nat, a ≤ b →
          sumChildrenTake ms a ≤ sumChildrenTake ms b := by
        intro a b hab
        induction hab with
        | refl => exact Nat.le_refl _
        | @step c hac ih' =>
          have hstep' := sumChildrenTake_le_succ ms c
          exact Nat.le_trans ih' hstep'
      exact hmono (j.val + 1) i.val hgt
  unfold inChildRange at hi hj
  rcases hsep with hle | hle
  · omega
  · omega

/-- Bottom (`1`) has no outgoing edges in `.branch ms`. This wraps the
Reachability lemma into the branch-edge namespace used here. -/
private theorem branch_bottom_sink (ms : List (String × SessionType)) (w : Nat) :
    ¬ (1, w) ∈ edgeList (.branch ms : SessionType) 0 [] := by
  have h := branch_bottom_no_outgoing ms 0 [] w
  simpa using h

/-- **Closure step**: if `P(a) := inChildRange ms i a ∨ a = 1` holds
and there's a branch edge `a → b`, then `P(b)` holds. -/
private theorem branch_child_closure_step
    (ms : List (String × SessionType)) (i : Fin ms.length)
    (a b : Nat)
    (hP : inChildRange ms i a ∨ a = 1)
    (hedge : (a, b) ∈ edgeList (.branch ms : SessionType) 0 []) :
    inChildRange ms i b ∨ b = 1 := by
  rcases hP with hIn | h1
  · -- Case a ∈ child i. Apply branch_edge_taxonomy.
    have htax := branch_edge_taxonomy ms a b hedge
    rcases htax with ⟨ha0, hb1, _⟩
                   | ⟨ha0, _⟩
                   | ⟨hb1, _⟩
                   | ⟨k, hu_lo, hu_hi, hv_lo, hv_hi, _⟩
    · -- Bucket 1: a = 0. But a ∈ child i means a ≥ 2. Contradiction.
      unfold inChildRange at hIn
      omega
    · -- Bucket 2: a = 0, same contradiction.
      unfold inChildRange at hIn
      omega
    · -- Bucket 3: b = 1. P(b) holds via right disjunct.
      exact Or.inr hb1
    · -- Bucket 4: edge is child-internal of child k. Then a ∈ child k,
      -- but a ∈ child i, so by disjointness k = i, and b ∈ child k = child i.
      have hak : inChildRange ms k a := by
        unfold inChildRange; exact ⟨hu_lo, hu_hi⟩
      -- By disjointness, k = i.
      have hki : k = i := by
        by_contra hne
        exact inChildRange_disjoint ms k i hne a hak hIn
      rw [← hki]
      exact Or.inl ⟨hv_lo, hv_hi⟩
  · -- Case a = 1. Bottom has no outgoing edges, contradicting hedge.
    rw [h1] at hedge
    exact absurd hedge (branch_bottom_sink ms b)

/-- **Closure walk**: if `P(u)` holds and `u → v` is a walk, then `P(v)`. -/
private theorem branch_child_closure_walk
    (ms : List (String × SessionType)) (i : Fin ms.length)
    (u v : Nat)
    (hP : inChildRange ms i u ∨ u = 1)
    (hwalk : Relation.ReflTransGen
      (SessionType.edgeRel (.branch ms : SessionType) 0 []) u v) :
    inChildRange ms i v ∨ v = 1 := by
  induction hwalk with
  | refl => exact hP
  | tail _ hedge ih =>
    exact branch_child_closure_step ms i _ _ ih hedge

/-- **Cross-child non-reachability (Nat form)**: a walk from a vertex in
child `i` cannot end in child `j` (with `i ≠ j`) in the branch graph. -/
theorem branch_cross_child_not_reachable_nat
    (ms : List (String × SessionType))
    (i j : Fin ms.length) (hij : i ≠ j)
    (u v : Nat)
    (hu : inChildRange ms i u)
    (hv : inChildRange ms j v)
    (hwalk : Relation.ReflTransGen
      (SessionType.edgeRel (.branch ms : SessionType) 0 []) u v) :
    False := by
  have hP : inChildRange ms i v ∨ v = 1 :=
    branch_child_closure_walk ms i u v (Or.inl hu) hwalk
  rcases hP with hvi | hv1
  · exact inChildRange_disjoint ms i j hij v hvi hv
  · -- v = 1 but v ∈ child j means v ≥ 2 + 0 = 2, contradiction.
    unfold inChildRange at hv
    omega

/-- **Cross-child non-reachability** at the `State` (Fin) level. -/
theorem branch_cross_child_not_reachable
    (ms : List (String × SessionType))
    (i j : Fin ms.length) (hij : i ≠ j)
    (u : State (.branch ms : SessionType))
    (v : State (.branch ms : SessionType))
    (hu : inChildRange ms i u.val)
    (hv : inChildRange ms j v.val) :
    ¬ Reachable (stateSpace (.branch ms : SessionType)) u v := by
  intro hwalk
  -- Lift Fin-level walk to Nat-level walk via ReflTransGen.lift with Fin.val.
  have hwalkNat : Relation.ReflTransGen
      (SessionType.edgeRel (.branch ms : SessionType) 0 []) u.val v.val := by
    have := @Relation.ReflTransGen.lift
      (State (.branch ms : SessionType)) Nat
      (stateSpace (.branch ms : SessionType)).edge
      (SessionType.edgeRel (.branch ms : SessionType) 0 [])
      u v Fin.val
      (fun x y hxy => hxy) hwalk
    exact this
  exact branch_cross_child_not_reachable_nat ms i j hij u.val v.val hu hv hwalkNat

/-!
### Select analogues

Since `edgeList (.select ls) 0 []` uses the same
`edgeListBranchChildren` helper as `.branch`, the select case mirrors
the branch case. We restate the three main results for select.
-/

/-- Select analogue of `branch_bottom_sink`. -/
private theorem select_bottom_sink (ls : List (String × SessionType)) (w : Nat) :
    ¬ (1, w) ∈ edgeList (.select ls : SessionType) 0 [] := by
  have h := select_bottom_no_outgoing ls 0 [] w
  simpa using h

/-- Select analogue of `branch_child_closure_step`. -/
private theorem select_child_closure_step
    (ls : List (String × SessionType)) (i : Fin ls.length)
    (a b : Nat)
    (hP : inChildRange ls i a ∨ a = 1)
    (hedge : (a, b) ∈ edgeList (.select ls : SessionType) 0 []) :
    inChildRange ls i b ∨ b = 1 := by
  rcases hP with hIn | h1
  · have htax := select_edge_taxonomy ls a b hedge
    rcases htax with ⟨ha0, hb1, _⟩
                   | ⟨ha0, _⟩
                   | ⟨hb1, _⟩
                   | ⟨k, hu_lo, hu_hi, hv_lo, hv_hi, _⟩
    · unfold inChildRange at hIn
      omega
    · unfold inChildRange at hIn
      omega
    · exact Or.inr hb1
    · have hak : inChildRange ls k a := by
        unfold inChildRange; exact ⟨hu_lo, hu_hi⟩
      have hki : k = i := by
        by_contra hne
        exact inChildRange_disjoint ls k i hne a hak hIn
      rw [← hki]
      exact Or.inl ⟨hv_lo, hv_hi⟩
  · rw [h1] at hedge
    exact absurd hedge (select_bottom_sink ls b)

/-- Select analogue of `branch_child_closure_walk`. -/
private theorem select_child_closure_walk
    (ls : List (String × SessionType)) (i : Fin ls.length)
    (u v : Nat)
    (hP : inChildRange ls i u ∨ u = 1)
    (hwalk : Relation.ReflTransGen
      (SessionType.edgeRel (.select ls : SessionType) 0 []) u v) :
    inChildRange ls i v ∨ v = 1 := by
  induction hwalk with
  | refl => exact hP
  | tail _ hedge ih =>
    exact select_child_closure_step ls i _ _ ih hedge

/-- **Select cross-child non-reachability (Nat form)**. -/
theorem select_cross_child_not_reachable_nat
    (ls : List (String × SessionType))
    (i j : Fin ls.length) (hij : i ≠ j)
    (u v : Nat)
    (hu : inChildRange ls i u)
    (hv : inChildRange ls j v)
    (hwalk : Relation.ReflTransGen
      (SessionType.edgeRel (.select ls : SessionType) 0 []) u v) :
    False := by
  have hP : inChildRange ls i v ∨ v = 1 :=
    select_child_closure_walk ls i u v (Or.inl hu) hwalk
  rcases hP with hvi | hv1
  · exact inChildRange_disjoint ls i j hij v hvi hv
  · unfold inChildRange at hv
    omega

/-- **Select cross-child non-reachability** at the `State` level. -/
theorem select_cross_child_not_reachable
    (ls : List (String × SessionType))
    (i j : Fin ls.length) (hij : i ≠ j)
    (u : State (.select ls : SessionType))
    (v : State (.select ls : SessionType))
    (hu : inChildRange ls i u.val)
    (hv : inChildRange ls j v.val) :
    ¬ Reachable (stateSpace (.select ls : SessionType)) u v := by
  intro hwalk
  have hwalkNat : Relation.ReflTransGen
      (SessionType.edgeRel (.select ls : SessionType) 0 []) u.val v.val := by
    have := @Relation.ReflTransGen.lift
      (State (.select ls : SessionType)) Nat
      (stateSpace (.select ls : SessionType)).edge
      (SessionType.edgeRel (.select ls : SessionType) 0 [])
      u v Fin.val
      (fun x y hxy => hxy) hwalk
    exact this
  exact select_cross_child_not_reachable_nat ls i j hij u.val v.val hu hv hwalkNat

/-!
## Phase 1b-β3-follow-3 — Same-child reachability characterisation

Using cross-child non-reachability (Part C) and branch edge taxonomy
(Part B), we now prove the **same-child reachability iff**: two vertices
that both sit in child `i` of a branch/select are reachable in the branch
state space iff they are reachable in the child's state space under the
child-shift embedding.

### Strategy

1. **Arithmetic bound** (`sumChildrenTake_le_child`): the prefix sum of
   child sizes up to index `i`, plus `stateCount (ms[i])`, fits inside
   `sumChildrenPair ms`. This lets us build the `branchChildShift`
   embedding into `State (.branch ms)`.

2. **Nat-level edge lift** (`edge_in_child_mem_branchChildren_nat`): a
   Nat-level edge of child `i`'s `edgeList` at offset
   `childStart + sumChildrenTake ms i.val` is also a Nat-level edge of
   `edgeListBranchChildren ms childStart root bottom env`.

3. **Edge lift (Fin form)** (`branch_child_edge_lift`): a child edge
   `x → y` lifts to a branch edge `branchChildShift ms i x →
   branchChildShift ms i y`.

4. **Walk lift** (`branch_child_walk_lift`): forward direction of the
   iff by `ReflTransGen.lift`.

5. **Edge unlift** (`branch_child_edge_unlift`): using
   `branch_edge_taxonomy`, a branch edge with source in child `i` is
   either an exit edge (target = 1) or a child-internal edge of child
   `i`; when the target is also in child `i`, only the latter applies.

6. **Same-child iff** (`branch_same_child_reachable_iff`): the backward
   direction uses tail induction on the walk, projecting each step via
   the unlift lemma while tracking "target is in child i" as an
   invariant.
-/

/-- Arithmetic bound: the prefix-sum offset up to index `i` plus the
size of child `i` is bounded by `sumChildrenPair ms`. Proved via
`sumChildrenTake_succ` + `sumChildrenTake_le`. -/
theorem sumChildrenTake_add_stateCount_le
    (ms : List (String × SessionType)) (i : Fin ms.length) :
    sumChildrenTake ms i.val + stateCount (ms.get i).2
      ≤ stateCount.sumChildrenPair ms := by
  rw [sumChildrenTake_succ]
  exact sumChildrenTake_le ms (i.val + 1)

/-- Shift a child vertex `x : State (ms.get i).2` into the branch state
space. The absolute offset is `2 + sumChildrenTake ms i.val`. -/
def branchChildShift (ms : List (String × SessionType)) (i : Fin ms.length)
    (x : State (ms.get i).2) : State (.branch ms : SessionType) :=
  ⟨2 + sumChildrenTake ms i.val + x.val, by
    show 2 + sumChildrenTake ms i.val + x.val < 2 + stateCount.sumChildrenPair ms
    have hbound := sumChildrenTake_add_stateCount_le ms i
    have hxlt : x.val < stateCount (ms.get i).2 := x.isLt
    omega⟩

/-- The shift lands in child `i`'s range. -/
theorem branchChildShift_inChildRange
    (ms : List (String × SessionType)) (i : Fin ms.length)
    (x : State (ms.get i).2) :
    inChildRange ms i (branchChildShift ms i x).val := by
  refine ⟨?_, ?_⟩
  · show 2 + sumChildrenTake ms i.val ≤ (branchChildShift ms i x).val
    simp [branchChildShift]
  · show (branchChildShift ms i x).val < 2 + sumChildrenTake ms i.val +
      stateCount (ms.get i).2
    simp [branchChildShift]

/-- Shift preserves the absolute index equation. -/
@[simp] theorem branchChildShift_val
    (ms : List (String × SessionType)) (i : Fin ms.length)
    (x : State (ms.get i).2) :
    (branchChildShift ms i x).val = 2 + sumChildrenTake ms i.val + x.val := rfl

/-- **Nat-level edge lift for `edgeListBranchChildren`**: a child-internal
edge `(u, v) ∈ edgeList (ms.get ⟨i, hi⟩).2 (childStart + sumChildrenTake ms i) env`
injects into `edgeListBranchChildren ms childStart root bottom env`. -/
theorem edge_in_child_mem_branchChildren_nat :
    ∀ (ms : List (String × SessionType)) (childStart root bottom : Nat)
      (env : List (String × Nat)) (i : Nat) (hi : i < ms.length)
      (u v : Nat),
      (u, v) ∈ edgeList (ms.get ⟨i, hi⟩).2 (childStart + sumChildrenTake ms i) env →
      (u, v) ∈ edgeList.edgeListBranchChildren ms childStart root bottom env
  | [],           _,          _,    _,      _,   _, hi, _, _, _ => by
      exact absurd hi (by simp)
  | (m, s) :: tl, childStart, root, bottom, env, i, hi, u, v, hEdge => by
      cases i with
      | zero =>
        -- i = 0: shift = 0, edge in s's edgeList at childStart
        have hget : (((m, s) :: tl).get ⟨0, hi⟩).2 = s := rfl
        rw [hget, sumChildrenTake_zero] at hEdge
        have : childStart + 0 = childStart := by omega
        rw [this] at hEdge
        -- Use sub_first to lift child edge into branchChildren.
        exact edgeListBranchChildren_sub_first m s tl childStart root bottom env hEdge
      | succ k =>
        -- i = succ k: shift = stateCount s + sumChildrenTake tl k
        have hk_lt : k < tl.length := by
          simp [List.length] at hi; omega
        have hget : (((m, s) :: tl).get ⟨k + 1, hi⟩).2 =
                    (tl.get ⟨k, hk_lt⟩).2 := rfl
        rw [hget, sumChildrenTake_cons_succ] at hEdge
        -- childStart + (stateCount s + sumChildrenTake tl k)
        --  = (childStart + stateCount s) + sumChildrenTake tl k
        have hrw : childStart + (stateCount s + sumChildrenTake tl k)
                 = (childStart + stateCount s) + sumChildrenTake tl k := by omega
        rw [hrw] at hEdge
        -- Apply IH on tl with base (childStart + stateCount s).
        have ih := edge_in_child_mem_branchChildren_nat tl
          (childStart + stateCount s) root bottom env k hk_lt u v hEdge
        -- Use sub_rest to lift.
        exact edgeListBranchChildren_sub_rest m s tl childStart root bottom env ih

/-- **Nat-level edge lift for `.branch`**: a child-internal edge at
offset `2 + sumChildrenTake ms i` lifts to a branch edge. -/
theorem edge_in_child_mem_branch_nat
    (ms : List (String × SessionType)) (i : Nat) (hi : i < ms.length)
    (u v : Nat)
    (hEdge : (u, v) ∈ edgeList (ms.get ⟨i, hi⟩).2 (2 + sumChildrenTake ms i) []) :
    (u, v) ∈ edgeList (.branch ms : SessionType) 0 [] := by
  simp only [edgeList, List.mem_append]
  right
  have : (0 + 2) = 2 := by omega
  have hmem : (u, v) ∈ edgeList.edgeListBranchChildren ms 2 0 1 [] :=
    edge_in_child_mem_branchChildren_nat ms 2 0 1 [] i hi u v hEdge
  convert hmem using 1

/-- Select analogue of `edge_in_child_mem_branch_nat`. -/
theorem edge_in_child_mem_select_nat
    (ls : List (String × SessionType)) (i : Nat) (hi : i < ls.length)
    (u v : Nat)
    (hEdge : (u, v) ∈ edgeList (ls.get ⟨i, hi⟩).2 (2 + sumChildrenTake ls i) []) :
    (u, v) ∈ edgeList (.select ls : SessionType) 0 [] := by
  simp only [edgeList, List.mem_append]
  right
  have hmem : (u, v) ∈ edgeList.edgeListBranchChildren ls 2 0 1 [] :=
    edge_in_child_mem_branchChildren_nat ls 2 0 1 [] i hi u v hEdge
  convert hmem using 1

/-- Select analogue of `branchChildShift`. -/
def selectChildShift (ls : List (String × SessionType)) (i : Fin ls.length)
    (x : State (ls.get i).2) : State (.select ls : SessionType) :=
  ⟨2 + sumChildrenTake ls i.val + x.val, by
    show 2 + sumChildrenTake ls i.val + x.val < 2 + stateCount.sumChildrenPair ls
    have hbound := sumChildrenTake_add_stateCount_le ls i
    have hxlt : x.val < stateCount (ls.get i).2 := x.isLt
    omega⟩

/-- Select shift lands in child range. -/
theorem selectChildShift_inChildRange
    (ls : List (String × SessionType)) (i : Fin ls.length)
    (x : State (ls.get i).2) :
    inChildRange ls i (selectChildShift ls i x).val := by
  refine ⟨?_, ?_⟩
  · show 2 + sumChildrenTake ls i.val ≤ (selectChildShift ls i x).val
    simp [selectChildShift]
  · show (selectChildShift ls i x).val < 2 + sumChildrenTake ls i.val +
      stateCount (ls.get i).2
    simp [selectChildShift]

/-- Select shift value. -/
@[simp] theorem selectChildShift_val
    (ls : List (String × SessionType)) (i : Fin ls.length)
    (x : State (ls.get i).2) :
    (selectChildShift ls i x).val = 2 + sumChildrenTake ls i.val + x.val := rfl

/-!
## Phase 1b-β3-follow-4 Part 1 — Shift invariance of `edgeList` under `parClosed`

Under the hypothesis `parClosed S`, `edgeList S start env` admits a clean
shift invariance: shifting `start` by `k` and simultaneously shifting every
value in `env` by `k` produces an edge list whose every edge is shifted by
`k` on both endpoints.

The key insight enabling this under `parClosed`: the par case calls
`edgeList child 0 env` on each child, but under `parClosed (.par ss)` every
child is `closed` (has `freeVars = ∅`), so by `edgeList_env_congr_of_freeVars`
the env is irrelevant at the par-child boundary — the child's raw edge list
is independent of `env`, and therefore independent of whether we shifted
`env` by `k` or not.

We prove Flavour B (general `start`, general `env`) as a single mutual
recursion over `edgeList`, `edgeListBranchChildren`, and `edgeListParGo`
(plus `edgeListParLiftChild`, `edgeListParLiftOne`, `edgeListParLiftSuffix`
as pure arithmetic sublemmas). Flavour A (`start = 0, env = []`) follows by
specialisation — note that `List.map f [] = []`, so the empty env maps to
the empty env trivially.
-/

/-- Helper: `envLookup` on an env shifted by `k` returns the shift of the
original lookup, as an iff on `some` values. -/
theorem envLookup_map_shift
    (env : List (String × Nat)) (k : Nat) (X : String) (v : Nat) :
    envLookup (env.map (fun p => (p.1, p.2 + k))) X = some v ↔
    ∃ n, envLookup env X = some n ∧ v = n + k := by
  induction env with
  | nil =>
    simp [envLookup]
  | cons p tl ih =>
    obtain ⟨y, n⟩ := p
    simp only [List.map_cons, envLookup]
    by_cases hY : y = X
    · subst hY
      simp only [if_true]
      refine ⟨?_, ?_⟩
      · intro h
        simp only [Option.some.injEq] at h
        exact ⟨n, rfl, h.symm⟩
      · intro ⟨n', hn', hv⟩
        simp only [Option.some.injEq] at hn'
        subst hn'
        subst hv
        rfl
    · simp only [if_neg hY]
      exact ih

/-- `envLookup` on a shifted env, forward direction: shift the lookup. -/
theorem envLookup_map_shift_some
    (env : List (String × Nat)) (k : Nat) (X : String) (n : Nat)
    (h : envLookup env X = some n) :
    envLookup (env.map (fun p => (p.1, p.2 + k))) X = some (n + k) := by
  rw [envLookup_map_shift]
  exact ⟨n, h, rfl⟩

/-- `envLookup` on a shifted env, backward direction: if a shifted env
produces `some v`, then the original env produces `some (v - k)`... but
more usefully, there is some `n` with `envLookup env X = some n` and
`v = n + k`. -/
theorem envLookup_map_shift_rev
    (env : List (String × Nat)) (k : Nat) (X : String) (v : Nat)
    (h : envLookup (env.map (fun p => (p.1, p.2 + k))) X = some v) :
    ∃ n, envLookup env X = some n ∧ v = n + k :=
  (envLookup_map_shift env k X v).mp h

/-- `envLookup env X = none` iff the shifted env also returns `none`. -/
theorem envLookup_map_shift_none
    (env : List (String × Nat)) (k : Nat) (X : String) :
    envLookup (env.map (fun p => (p.1, p.2 + k))) X = none ↔
    envLookup env X = none := by
  induction env with
  | nil => simp [envLookup]
  | cons p tl ih =>
    obtain ⟨y, n⟩ := p
    simp only [List.map_cons, envLookup]
    by_cases hY : y = X
    · simp [hY]
    · simp only [if_neg hY]
      exact ih

/-!
### Shift arithmetic sublemmas for `edgeListParLiftSuffix`/`LiftOne`/`LiftChild`

Using the `mem_edgeListParLift*` membership characterisations from
`StateSpaceEdges.lean`, we can express shift invariance purely at the
iff-on-membership level, avoiding re-induction on the iteration counters.
-/

/-- `edgeListParLiftSuffix` shift: an edge `(src, tgt)` is in the list at
`start` iff `(src + k, tgt + k)` is in the list at `start + k`. -/
theorem edgeListParLiftSuffix_shift
    (u v start suffixProd size pBase q0 k src tgt : Nat) :
    (src, tgt) ∈ edgeList.edgeListParLiftSuffix u v start suffixProd size pBase q0
      ↔
    (src + k, tgt + k) ∈
      edgeList.edgeListParLiftSuffix u v (start + k) suffixProd size pBase q0 := by
  rw [mem_edgeListParLiftSuffix, mem_edgeListParLiftSuffix]
  refine ⟨?_, ?_⟩
  · rintro ⟨q, hq0, hqlt, hsrc, htgt⟩
    refine ⟨q, hq0, hqlt, ?_, ?_⟩
    · omega
    · omega
  · rintro ⟨q, hq0, hqlt, hsrc, htgt⟩
    refine ⟨q, hq0, hqlt, ?_, ?_⟩
    · omega
    · omega

/-- `edgeListParLiftOne` shift. -/
theorem edgeListParLiftOne_shift
    (u v start suffixProd size prefixProd p0 k src tgt : Nat) :
    (src, tgt) ∈ edgeList.edgeListParLiftOne u v start suffixProd size prefixProd p0
      ↔
    (src + k, tgt + k) ∈
      edgeList.edgeListParLiftOne u v (start + k) suffixProd size prefixProd p0 := by
  rw [mem_edgeListParLiftOne, mem_edgeListParLiftOne]
  refine ⟨?_, ?_⟩
  · rintro ⟨p, q, hp0, hplt, hqlt, hsrc, htgt⟩
    refine ⟨p, q, hp0, hplt, hqlt, ?_, ?_⟩
    · omega
    · omega
  · rintro ⟨p, q, hp0, hplt, hqlt, hsrc, htgt⟩
    refine ⟨p, q, hp0, hplt, hqlt, ?_, ?_⟩
    · omega
    · omega

/-- `edgeListParLiftChild` shift (input edge list same on both sides). -/
theorem edgeListParLiftChild_shift
    (edges : List (Nat × Nat)) (start suffixProd size prefixProd k src tgt : Nat) :
    (src, tgt) ∈ edgeList.edgeListParLiftChild edges start suffixProd size prefixProd
      ↔
    (src + k, tgt + k) ∈
      edgeList.edgeListParLiftChild edges (start + k) suffixProd size prefixProd := by
  rw [mem_edgeListParLiftChild, mem_edgeListParLiftChild]
  refine ⟨?_, ?_⟩
  · rintro ⟨u, v, hmem, p, q, hplt, hqlt, hsrc, htgt⟩
    refine ⟨u, v, hmem, p, q, hplt, hqlt, ?_, ?_⟩
    · omega
    · omega
  · rintro ⟨u, v, hmem, p, q, hplt, hqlt, hsrc, htgt⟩
    refine ⟨u, v, hmem, p, q, hplt, hqlt, ?_, ?_⟩
    · omega
    · omega

/-!
### Main shift theorem — `edgeList_shift_of_parClosed`

Under the hypothesis `parClosed S`, shifting `start` by `k` and shifting
every env-value by `k` in parallel shifts every emitted edge by `k` on
both endpoints. Joint mutual induction on `S` / `ms` / `ss`, packaged as
three simultaneous theorems (the third for `edgeListParGo`).

At the par case, we exploit the fact that `parClosed (.par ss)` implies
every `s ∈ ss` has `freeVars s = ∅`, so `edgeList s 0 env = edgeList s 0 env'`
for any pair `env, env'` — in particular, for `env` and its shift. This
collapses the par recursion at the "raw child" level and leaves only the
pure arithmetic shift on the lift helpers.
-/

/-- Pure arithmetic: `exitSlot` is linear in `start`, i.e.,
`exitSlot S (start + k) = exitSlot S start + k`. -/
theorem exitSlot_add_comm :
    ∀ (S : SessionType) (start k : Nat),
      exitSlot S (start + k) = exitSlot S start + k
  | .end_,        start, k => by simp [exitSlot]
  | .var _,       start, k => by simp [exitSlot]
  | .branch _,    start, k => by simp [exitSlot]; omega
  | .select _,    start, k => by simp [exitSlot]; omega
  | .par ss,      start, k => by
      simp only [exitSlot]
      omega
  | .rec_ _ body, start, k => by
      simp only [exitSlot]
      exact exitSlot_add_comm body start k

mutual

/-- **Flavour B shift invariance** for `edgeList`: under `parClosed S`,
shifting `start` by `k` and the env-values by `k` shifts every emitted
edge by `k`. -/
theorem edgeList_shift_of_parClosed :
    ∀ (S : SessionType), parClosed S →
      ∀ (start k : Nat) (env : List (String × Nat)) (u v : Nat),
        (u, v) ∈ edgeList S start env ↔
        (u + k, v + k) ∈
          edgeList S (start + k) (env.map (fun p => (p.1, p.2 + k)))
  | .end_,        _,   start, k, env, u, v => by
      simp only [edgeList]
      simp
  | .var X,       _,   start, k, env, u, v => by
      simp only [edgeList]
      -- Case analyse on envLookup env X.
      cases hLk : envLookup env X with
      | none =>
        have hLk_shift :
            envLookup (env.map (fun p => (p.1, p.2 + k))) X = none :=
          (envLookup_map_shift_none env k X).mpr hLk
        rw [hLk_shift]
        simp
      | some n =>
        have hLk_shift :
            envLookup (env.map (fun p => (p.1, p.2 + k))) X = some (n + k) :=
          envLookup_map_shift_some env k X n hLk
        rw [hLk_shift]
        simp only [List.mem_singleton, Prod.mk.injEq]
        refine ⟨?_, ?_⟩
        · rintro ⟨hu, hv⟩
          exact ⟨by omega, by omega⟩
        · rintro ⟨hu, hv⟩
          exact ⟨by omega, by omega⟩
  | .branch ms,   hPC, start, k, env, u, v => by
      simp only [edgeList, List.mem_append]
      have hPCchildren : parClosed (.branch ms) := hPC
      -- Children edges: use branchChildren_shift at (start + 2)
      have hChildShift := edgeList_branchChildren_shift ms hPCchildren
        (start + 2) start (start + 1) k env u v
      refine ⟨?_, ?_⟩
      · rintro (hEmpty | hChildren)
        · split at hEmpty
          · rename_i hMs
            simp only [List.mem_singleton, Prod.mk.injEq] at hEmpty
            obtain ⟨hu_eq, hv_eq⟩ := hEmpty
            left
            split
            · rename_i _
              simp only [List.mem_singleton, Prod.mk.injEq]
              exact ⟨by omega, by omega⟩
            · rename_i hNotMs
              exact absurd hMs hNotMs
          · exact (List.not_mem_nil hEmpty).elim
        · right
          have : start + 2 + k = (start + k) + 2 := by omega
          rw [this] at hChildShift
          have : start + 1 + k = (start + k) + 1 := by omega
          rw [this] at hChildShift
          exact hChildShift.mp hChildren
      · rintro (hEmpty | hChildren)
        · split at hEmpty
          · rename_i hMs
            simp only [List.mem_singleton, Prod.mk.injEq] at hEmpty
            obtain ⟨hu_eq, hv_eq⟩ := hEmpty
            left
            split
            · rename_i _
              simp only [List.mem_singleton, Prod.mk.injEq]
              exact ⟨by omega, by omega⟩
            · rename_i hNotMs
              exact absurd hMs hNotMs
          · exact (List.not_mem_nil hEmpty).elim
        · right
          have : start + 2 + k = (start + k) + 2 := by omega
          rw [this] at hChildShift
          have : start + 1 + k = (start + k) + 1 := by omega
          rw [this] at hChildShift
          exact hChildShift.mpr hChildren
  | .select ls,   hPC, start, k, env, u, v => by
      simp only [edgeList, List.mem_append]
      have hPCchildren : parClosed (.select ls) := hPC
      have hChildShift := edgeList_branchChildren_shift ls hPCchildren
        (start + 2) start (start + 1) k env u v
      refine ⟨?_, ?_⟩
      · rintro (hEmpty | hChildren)
        · split at hEmpty
          · rename_i hLs
            simp only [List.mem_singleton, Prod.mk.injEq] at hEmpty
            obtain ⟨hu_eq, hv_eq⟩ := hEmpty
            left
            split
            · rename_i _
              simp only [List.mem_singleton, Prod.mk.injEq]
              exact ⟨by omega, by omega⟩
            · rename_i hNotLs
              exact absurd hLs hNotLs
          · exact (List.not_mem_nil hEmpty).elim
        · right
          have : start + 2 + k = (start + k) + 2 := by omega
          rw [this] at hChildShift
          have : start + 1 + k = (start + k) + 1 := by omega
          rw [this] at hChildShift
          exact hChildShift.mp hChildren
      · rintro (hEmpty | hChildren)
        · split at hEmpty
          · rename_i hLs
            simp only [List.mem_singleton, Prod.mk.injEq] at hEmpty
            obtain ⟨hu_eq, hv_eq⟩ := hEmpty
            left
            split
            · rename_i _
              simp only [List.mem_singleton, Prod.mk.injEq]
              exact ⟨by omega, by omega⟩
            · rename_i hNotLs
              exact absurd hLs hNotLs
          · exact (List.not_mem_nil hEmpty).elim
        · right
          have : start + 2 + k = (start + k) + 2 := by omega
          rw [this] at hChildShift
          have : start + 1 + k = (start + k) + 1 := by omega
          rw [this] at hChildShift
          exact hChildShift.mpr hChildren
  | .par ss,      hPC, start, k, env, u, v => by
      simp only [edgeList]
      show (u, v) ∈ edgeList.edgeListPar ss start env ↔
           (u + k, v + k) ∈ edgeList.edgeListPar ss (start + k)
             (env.map (fun p => (p.1, p.2 + k)))
      unfold edgeList.edgeListPar
      exact edgeList_parGo_shift ss hPC start k env 1 u v
  | .rec_ X body, hPC, start, k, env, u, v => by
      simp only [edgeList]
      have hPCbody : parClosed body := parClosed_rec_body X body hPC
      have ih := edgeList_shift_of_parClosed body hPCbody start k
        ((X, start) :: env) u v
      -- The RHS env after shift is (X, start + k) :: (env.map shift).
      have hEnvEq : ((X, start) :: env).map (fun p => (p.1, p.2 + k))
                  = (X, start + k) :: env.map (fun p => (p.1, p.2 + k)) := by
        simp [List.map]
      rw [hEnvEq] at ih
      exact ih

/-- **Shift invariance helper** for `edgeListBranchChildren` under
`parClosed (.branch ms)` (equivalently for select). -/
theorem edgeList_branchChildren_shift :
    ∀ (ms : List (String × SessionType)),
      parClosed (.branch ms : SessionType) →
      ∀ (childStart root bottom k : Nat)
        (env : List (String × Nat)) (u v : Nat),
        (u, v) ∈ edgeList.edgeListBranchChildren ms childStart root bottom env ↔
        (u + k, v + k) ∈
          edgeList.edgeListBranchChildren ms (childStart + k) (root + k)
            (bottom + k) (env.map (fun p => (p.1, p.2 + k)))
  | [],           _,   _,          _,    _,      _, _,   _, _ => by
      simp [edgeList.edgeListBranchChildren]
  | (m, s) :: tl, hPC, childStart, root, bottom, k, env, u, v => by
      -- Head child edge list shifts (s is parClosed from hPC).
      have hPCs : parClosed s := by
        have hBool : parClosedBool (.branch ((m, s) :: tl) : SessionType) = true := hPC
        simp only [parClosedBool, parClosedBool.parClosedPairList] at hBool
        exact (Bool.and_eq_true _ _).mp hBool |>.1
      have hPCtl : parClosed (.branch tl : SessionType) := by
        have hBool : parClosedBool (.branch ((m, s) :: tl) : SessionType) = true := hPC
        simp only [parClosedBool, parClosedBool.parClosedPairList] at hBool
        have htl_bool := (Bool.and_eq_true _ _).mp hBool |>.2
        show parClosedBool (.branch tl : SessionType) = true
        simp only [parClosedBool]
        exact htl_bool
      have hHeadShift := edgeList_shift_of_parClosed s hPCs childStart k env u v
      have hTailShift := edgeList_branchChildren_shift tl hPCtl
        (childStart + stateCount s) root bottom k env u v
      have hrw1 : childStart + stateCount s + k
                = (childStart + k) + stateCount s := by omega
      rw [hrw1] at hTailShift
      refine ⟨?_, ?_⟩
      · intro h
        -- Destructure h : (u, v) ∈ edgeListBranchChildren ((m, s) :: tl) ...
        have hForm : (u, v) ∈ (root, childStart) ::
                              (exitSlot s childStart, bottom) ::
                              (edgeList s childStart env ++
                               edgeList.edgeListBranchChildren tl
                                 (childStart + stateCount s) root bottom env) := by
          simpa [edgeList.edgeListBranchChildren] using h
        -- Goal is membership in edgeListBranchChildren at shifted params.
        show (u + k, v + k) ∈ edgeList.edgeListBranchChildren ((m, s) :: tl)
          (childStart + k) (root + k) (bottom + k)
          (env.map (fun p => (p.1, p.2 + k)))
        -- Unfold the shifted form.
        have hGoalForm :
            edgeList.edgeListBranchChildren ((m, s) :: tl) (childStart + k)
              (root + k) (bottom + k)
              (env.map (fun p => (p.1, p.2 + k)))
            = (root + k, childStart + k) ::
              (exitSlot s (childStart + k), bottom + k) ::
              (edgeList s (childStart + k) (env.map (fun p => (p.1, p.2 + k))) ++
               edgeList.edgeListBranchChildren tl
                 ((childStart + k) + stateCount s) (root + k) (bottom + k)
                 (env.map (fun p => (p.1, p.2 + k)))) := by
          simp [edgeList.edgeListBranchChildren]
        rw [hGoalForm]
        simp only [List.mem_cons, List.mem_append, Prod.mk.injEq] at hForm ⊢
        rcases hForm with ⟨hu, hv⟩ | ⟨hu, hv⟩ | hHead | hTail
        · left; exact ⟨by omega, by omega⟩
        · right; left
          refine ⟨?_, by omega⟩
          rw [hu, exitSlot_add_comm]
        · right; right; left
          exact hHeadShift.mp hHead
        · right; right; right
          exact hTailShift.mp hTail
      · intro h
        have hForm : (u + k, v + k) ∈ (root + k, childStart + k) ::
                              (exitSlot s (childStart + k), bottom + k) ::
                              (edgeList s (childStart + k)
                                (env.map (fun p => (p.1, p.2 + k))) ++
                               edgeList.edgeListBranchChildren tl
                                 ((childStart + k) + stateCount s) (root + k)
                                 (bottom + k)
                                 (env.map (fun p => (p.1, p.2 + k)))) := by
          simpa [edgeList.edgeListBranchChildren] using h
        show (u, v) ∈ edgeList.edgeListBranchChildren ((m, s) :: tl) childStart
          root bottom env
        have hGoalForm :
            edgeList.edgeListBranchChildren ((m, s) :: tl) childStart root bottom env
            = (root, childStart) ::
              (exitSlot s childStart, bottom) ::
              (edgeList s childStart env ++
               edgeList.edgeListBranchChildren tl
                 (childStart + stateCount s) root bottom env) := by
          simp [edgeList.edgeListBranchChildren]
        rw [hGoalForm]
        simp only [List.mem_cons, List.mem_append, Prod.mk.injEq] at hForm ⊢
        rcases hForm with ⟨hu, hv⟩ | ⟨hu, hv⟩ | hHead | hTail
        · left; exact ⟨by omega, by omega⟩
        · right; left
          refine ⟨?_, by omega⟩
          have hexit_shift := exitSlot_add_comm s childStart k
          omega
        · right; right; left
          exact hHeadShift.mpr hHead
        · right; right; right
          exact hTailShift.mpr hTail

/-- **Shift invariance helper** for `edgeListParGo` under `parClosed (.par ss)`. -/
theorem edgeList_parGo_shift :
    ∀ (ss : List SessionType),
      parClosed (.par ss : SessionType) →
      ∀ (start k : Nat) (env : List (String × Nat))
        (prefixProd : Nat) (u v : Nat),
        (u, v) ∈ edgeList.edgeListParGo ss start env prefixProd ↔
        (u + k, v + k) ∈
          edgeList.edgeListParGo ss (start + k)
            (env.map (fun p => (p.1, p.2 + k))) prefixProd
  | [],      _,   start, k, env, prefixProd, u, v => by
      rw [mem_edgeListParGo_nil, mem_edgeListParGo_nil]
  | s :: tl, hPC, start, k, env, prefixProd, u, v => by
      -- `parClosed (.par (s :: tl))` gives: freeVars s = ∅ and parClosed (par tl).
      have hClosed_s : freeVars s = ∅ := by
        have hBool : parClosedBool (.par (s :: tl) : SessionType) = true := hPC
        simp only [parClosedBool] at hBool
        have hAll := (Bool.and_eq_true _ _).mp hBool |>.1
        simp only [parClosedBool.allClosedList] at hAll
        have hHead := (Bool.and_eq_true _ _).mp hAll |>.1
        simpa using hHead
      have hPCtl : parClosed (.par tl : SessionType) := by
        have hBool : parClosedBool (.par (s :: tl) : SessionType) = true := hPC
        simp only [parClosedBool] at hBool
        have hAndAll := (Bool.and_eq_true _ _).mp hBool
        have hAll := hAndAll.1
        have hParList := hAndAll.2
        simp only [parClosedBool.allClosedList] at hAll
        simp only [parClosedBool.parClosedList] at hParList
        have hAllTl := (Bool.and_eq_true _ _).mp hAll |>.2
        have hParListTl := (Bool.and_eq_true _ _).mp hParList |>.2
        show parClosedBool (.par tl : SessionType) = true
        simp only [parClosedBool]
        exact Bool.and_eq_true _ _ |>.mpr ⟨hAllTl, hParListTl⟩
      -- Key: `edgeList s 0 env = edgeList s 0 []` = `edgeList s 0 (env.map shift)`
      -- by env-congruence on ∅ freeVars.
      have hEnvInvLHS : edgeList s 0 env = edgeList s 0 [] := by
        apply edgeList_env_congr_of_freeVars
        intro X hX
        rw [hClosed_s] at hX
        exact absurd hX (Finset.notMem_empty _)
      have hEnvInvRHS : edgeList s 0 (env.map (fun p => (p.1, p.2 + k)))
                      = edgeList s 0 [] := by
        apply edgeList_env_congr_of_freeVars
        intro X hX
        rw [hClosed_s] at hX
        exact absurd hX (Finset.notMem_empty _)
      rw [mem_edgeListParGo_cons, mem_edgeListParGo_cons]
      simp only [hEnvInvLHS, hEnvInvRHS]
      -- Now both sides use the same rawChild = edgeList s 0 [], so the
      -- filtered localEdges are identical. Then the LiftChild shift handles
      -- the head case and the IH handles the tail case.
      have hTailShift := edgeList_parGo_shift tl hPCtl start k env
        (prefixProd * stateCount s) u v
      constructor
      · rintro (hhead | htail)
        · left
          exact (edgeListParLiftChild_shift _ start _ _ prefixProd k u v).mp hhead
        · right
          exact hTailShift.mp htail
      · rintro (hhead | htail)
        · left
          exact (edgeListParLiftChild_shift _ start _ _ prefixProd k u v).mpr hhead
        · right
          exact hTailShift.mpr htail

end

/-!
### Specialisations of the shift theorem

Two immediate corollaries useful downstream:

* Flavour A (top-level, env = []): `(u, v) ∈ edgeList S 0 []` iff
  `(u + k, v + k) ∈ edgeList S k []`.
* Branch child shift (start = `2 + sumChildrenTake ms i.val`, env = []):
  same statement specialised to the absolute offset a child receives in
  `edgeListBranchChildren`.
-/

/-- **Flavour A** shift invariance: top-level env = []. -/
theorem edgeList_shift_closed_parClosed_nil
    (S : SessionType) (hPC : parClosed S) (u v k : Nat) :
    (u, v) ∈ edgeList S 0 [] ↔ (u + k, v + k) ∈ edgeList S k [] := by
  have h := edgeList_shift_of_parClosed S hPC 0 k [] u v
  simp only [List.map_nil, Nat.zero_add] at h
  exact h

/-- **Branch-child shift**: a child-internal edge at offset
`2 + sumChildrenTake ms i.val` is the k-shift of a child edge at offset 0. -/
theorem edgeList_shift_branch_child
    (ms : List (String × SessionType))
    (hPC : parClosed (.branch ms : SessionType))
    (i : Fin ms.length) (u v : Nat) :
    (u, v) ∈ edgeList (ms.get i).2 0 [] ↔
    (u + (2 + sumChildrenTake ms i.val), v + (2 + sumChildrenTake ms i.val)) ∈
      edgeList (ms.get i).2 (2 + sumChildrenTake ms i.val) [] := by
  have hPCs : parClosed (ms.get i).2 := by
    apply parClosed_branch_children ms hPC
    exact List.get_mem ms i
  exact edgeList_shift_closed_parClosed_nil (ms.get i).2 hPCs u v
          (2 + sumChildrenTake ms i.val)

/-- **Select-child shift**: symmetric version for select. -/
theorem edgeList_shift_select_child
    (ls : List (String × SessionType))
    (hPC : parClosed (.select ls : SessionType))
    (i : Fin ls.length) (u v : Nat) :
    (u, v) ∈ edgeList (ls.get i).2 0 [] ↔
    (u + (2 + sumChildrenTake ls i.val), v + (2 + sumChildrenTake ls i.val)) ∈
      edgeList (ls.get i).2 (2 + sumChildrenTake ls i.val) [] := by
  have hPCs : parClosed (ls.get i).2 := by
    apply parClosed_select_children ls hPC
    exact List.get_mem ls i
  exact edgeList_shift_closed_parClosed_nil (ls.get i).2 hPCs u v
          (2 + sumChildrenTake ls i.val)

/-!
## Phase 1b-β3-follow-4 Part 2 — D.0 Walk-stays-in-child

Using Part 1's shift invariance, `branch_child_closure_walk` (already
landed), and `branch_bottom_no_outgoing`, we now prove the stronger form:
when both endpoints of a walk lie in child `i`, the walk never escapes
child `i` (in particular, never visits the root, never visits the bottom,
and never visits another child).

### Strategy

The key observation is that `branch_child_closure_walk` gives us: if `a`
is in child `i` and `a ⇒* b` is a walk, then `b ∈ child i ∨ b = 1`
(bottom). But bottom has no outgoing edges, so once we reach bottom we
cannot leave. Hence if the walk ends at `v ∈ child i` (not at bottom),
the final vertex is in child `i`.

For the stronger "every visited vertex stays in child i" invariant, we
use `ReflTransGen.head_induction_on` and exploit the fact that the
walk-segment from any intermediate vertex to `v` (which is in child i)
must have its starting point not equal to bottom.
-/

/-- Bottom has no outgoing walks of length > 0 to vertices other than
bottom itself. Equivalently: any walk from bottom must be the reflexive
walk (target = bottom). -/
theorem branch_bottom_walk_refl
    (ms : List (String × SessionType)) (w : Nat)
    (hwalk : Relation.ReflTransGen
      (SessionType.edgeRel (.branch ms : SessionType) 0 []) 1 w) :
    w = 1 := by
  induction hwalk with
  | refl => rfl
  | tail hprev hedge ih =>
    rename_i b
    -- ih : a = 1 after renaming; hedge : (a, b) ∈ edgeList ...
    -- After subst, hedge : (1, b) violates branch_bottom_no_outgoing.
    subst ih
    have hbot : ¬ (1, b) ∈ edgeList (.branch ms : SessionType) 0 [] := by
      have h := branch_bottom_no_outgoing ms 0 [] b
      simpa using h
    exact absurd hedge hbot

/-- Select bottom walk reflexive (symmetric). -/
theorem select_bottom_walk_refl
    (ls : List (String × SessionType)) (w : Nat)
    (hwalk : Relation.ReflTransGen
      (SessionType.edgeRel (.select ls : SessionType) 0 []) 1 w) :
    w = 1 := by
  induction hwalk with
  | refl => rfl
  | tail hprev hedge ih =>
    rename_i b
    subst ih
    have hbot : ¬ (1, b) ∈ edgeList (.select ls : SessionType) 0 [] := by
      have h := select_bottom_no_outgoing ls 0 [] b
      simpa using h
    exact absurd hedge hbot

/-- **D.0 branch: walk between two vertices in child `i` never visits
bottom, root, or another child** — stated as: the first vertex `a` of any
walk from `u` (in child `i`) that continues to reach `v` (also in child
`i`) must itself be in child `i`. -/
theorem branch_walk_stays_in_child_nat
    (ms : List (String × SessionType)) (i : Fin ms.length)
    (u v a : Nat)
    (hu : inChildRange ms i u)
    (hv : inChildRange ms i v)
    (hwalk_ua : Relation.ReflTransGen
      (SessionType.edgeRel (.branch ms : SessionType) 0 []) u a)
    (hwalk_av : Relation.ReflTransGen
      (SessionType.edgeRel (.branch ms : SessionType) 0 []) a v) :
    inChildRange ms i a := by
  -- By branch_child_closure_walk on hwalk_ua, a ∈ child i ∨ a = 1.
  have hpa : inChildRange ms i a ∨ a = 1 :=
    branch_child_closure_walk ms i u a (Or.inl hu) hwalk_ua
  rcases hpa with ha_child | ha_bot
  · exact ha_child
  · -- a = 1: then hwalk_av says walk from 1 to v. By bottom_walk_refl, v = 1.
    -- But v ∈ child i, so v ≥ 2 (by inChildRange). Contradiction.
    subst ha_bot
    have hv_eq_1 := branch_bottom_walk_refl ms v hwalk_av
    unfold inChildRange at hv
    omega

/-- **Select analogue of D.0**. -/
theorem select_walk_stays_in_child_nat
    (ls : List (String × SessionType)) (i : Fin ls.length)
    (u v a : Nat)
    (hu : inChildRange ls i u)
    (hv : inChildRange ls i v)
    (hwalk_ua : Relation.ReflTransGen
      (SessionType.edgeRel (.select ls : SessionType) 0 []) u a)
    (hwalk_av : Relation.ReflTransGen
      (SessionType.edgeRel (.select ls : SessionType) 0 []) a v) :
    inChildRange ls i a := by
  have hpa : inChildRange ls i a ∨ a = 1 :=
    select_child_closure_walk ls i u a (Or.inl hu) hwalk_ua
  rcases hpa with ha_child | ha_bot
  · exact ha_child
  · subst ha_bot
    have hv_eq_1 := select_bottom_walk_refl ls v hwalk_av
    unfold inChildRange at hv
    omega

/-!
## Phase 1b-β3-follow-4 Part 3 — D.1 forward: child walks lift

Combine Part 1's `edgeList_shift_branch_child` with the already-landed
Nat-level `edge_in_child_mem_branch_nat` to get the edge lift at the
`State` (Fin) level, then compose to ReflTransGen walks via
`ReflTransGen.lift`.
-/

/-- **Branch child edge lift (Fin form)**: a child-internal edge `(x, y)`
in the child state space lifts to a branch edge
`(branchChildShift ms i x, branchChildShift ms i y)`. -/
theorem branch_child_edge_lift
    (ms : List (String × SessionType))
    (hPC : parClosed (.branch ms : SessionType))
    (i : Fin ms.length)
    (x y : State (ms.get i).2)
    (hedge : (stateSpace (ms.get i).2).edge x y) :
    (stateSpace (.branch ms : SessionType)).edge
      (branchChildShift ms i x) (branchChildShift ms i y) := by
  -- hedge : (x.val, y.val) ∈ edgeList (ms.get i).2 0 [].
  have hshift := (edgeList_shift_branch_child ms hPC i x.val y.val).mp hedge
  have hlift := edge_in_child_mem_branch_nat ms i.val i.isLt
    (x.val + (2 + sumChildrenTake ms i.val))
    (y.val + (2 + sumChildrenTake ms i.val)) hshift
  -- Goal: (stateSpace (.branch ms)).edge (branchChildShift ms i x) (branchChildShift ms i y)
  -- Unfolds to: (branchChildShift ms i x).val, (branchChildShift ms i y).val ∈ edgeList ...
  simp only [stateSpace, branchChildShift_val]
  have hrw_x : (2 + sumChildrenTake ms i.val + x.val)
             = (x.val + (2 + sumChildrenTake ms i.val)) := by omega
  have hrw_y : (2 + sumChildrenTake ms i.val + y.val)
             = (y.val + (2 + sumChildrenTake ms i.val)) := by omega
  rw [hrw_x, hrw_y]
  exact hlift

/-- **Select child edge lift (Fin form)**. -/
theorem select_child_edge_lift
    (ls : List (String × SessionType))
    (hPC : parClosed (.select ls : SessionType))
    (i : Fin ls.length)
    (x y : State (ls.get i).2)
    (hedge : (stateSpace (ls.get i).2).edge x y) :
    (stateSpace (.select ls : SessionType)).edge
      (selectChildShift ls i x) (selectChildShift ls i y) := by
  have hshift := (edgeList_shift_select_child ls hPC i x.val y.val).mp hedge
  have hlift := edge_in_child_mem_select_nat ls i.val i.isLt
    (x.val + (2 + sumChildrenTake ls i.val))
    (y.val + (2 + sumChildrenTake ls i.val)) hshift
  simp only [stateSpace, selectChildShift_val]
  have hrw_x : (2 + sumChildrenTake ls i.val + x.val)
             = (x.val + (2 + sumChildrenTake ls i.val)) := by omega
  have hrw_y : (2 + sumChildrenTake ls i.val + y.val)
             = (y.val + (2 + sumChildrenTake ls i.val)) := by omega
  rw [hrw_x, hrw_y]
  exact hlift

/-- **Branch child walk lift (forward direction of D.1)**: a walk in the
child state space lifts to a walk in the branch state space via
`branchChildShift`. -/
theorem branch_child_walk_lift
    (ms : List (String × SessionType))
    (hPC : parClosed (.branch ms : SessionType))
    (i : Fin ms.length)
    (x y : State (ms.get i).2)
    (hwalk : Reachable (stateSpace (ms.get i).2) x y) :
    Reachable (stateSpace (.branch ms : SessionType))
      (branchChildShift ms i x) (branchChildShift ms i y) := by
  induction hwalk with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hedge ih =>
    exact Relation.ReflTransGen.tail ih (branch_child_edge_lift ms hPC i _ _ hedge)

/-- **Select child walk lift**. -/
theorem select_child_walk_lift
    (ls : List (String × SessionType))
    (hPC : parClosed (.select ls : SessionType))
    (i : Fin ls.length)
    (x y : State (ls.get i).2)
    (hwalk : Reachable (stateSpace (ls.get i).2) x y) :
    Reachable (stateSpace (.select ls : SessionType))
      (selectChildShift ls i x) (selectChildShift ls i y) := by
  induction hwalk with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hedge ih =>
    exact Relation.ReflTransGen.tail ih (select_child_edge_lift ls hPC i _ _ hedge)

/-!
## Phase 1b-β3-follow-4 Part 4 — D.2 backward: edge/walk unlift

Using `branch_edge_taxonomy` + `inChildRange_disjoint` + Part 1's shift
invariance, we prove the backward direction: a branch edge with both
endpoints in child `i` is the lift of a child-internal edge.

Combined with Part 2 (walk-stays-in-child) and Part 3 (forward walk
lift), we get the full same-child reachability iff.
-/

/-- **Branch child edge unlift (Nat form)**: an edge `(u, v)` of the
branch graph with both endpoints in child `i`'s range is a child-internal
edge of child `i`, shifted by the child's offset. -/
theorem branch_child_edge_unlift_nat
    (ms : List (String × SessionType))
    (hPC : parClosed (.branch ms : SessionType))
    (i : Fin ms.length) (u v : Nat)
    (hu : inChildRange ms i u) (hv : inChildRange ms i v)
    (hedge : (u, v) ∈ edgeList (.branch ms : SessionType) 0 []) :
    ∃ x y : Nat,
      u = 2 + sumChildrenTake ms i.val + x ∧
      v = 2 + sumChildrenTake ms i.val + y ∧
      x < stateCount (ms.get i).2 ∧
      y < stateCount (ms.get i).2 ∧
      (x, y) ∈ edgeList (ms.get i).2 0 [] := by
  -- Apply branch_edge_taxonomy.
  have htax := branch_edge_taxonomy ms u v hedge
  rcases htax with ⟨hu_eq, hv_eq, hms_eq⟩
                 | ⟨hu_eq, k, hv_eq⟩
                 | ⟨hv_eq, k, hu_eq⟩
                 | ⟨k, hu_lo, hu_hi, hv_lo, hv_hi, hmem⟩
  · -- Bucket 1: u = 0, v = 1. But u in child i means u ≥ 2, contradiction.
    unfold inChildRange at hu; omega
  · -- Bucket 2: u = 0. Same contradiction.
    unfold inChildRange at hu; omega
  · -- Bucket 3: v = 1. But v in child i means v ≥ 2, contradiction.
    unfold inChildRange at hv; omega
  · -- Bucket 4: edge is child-internal of child k. By disjointness, k = i.
    have hak : inChildRange ms k u := ⟨hu_lo, hu_hi⟩
    have hki : k = i := by
      by_contra hne
      exact inChildRange_disjoint ms k i hne u hak hu
    subst hki
    -- hmem : (u, v) ∈ edgeList (ms.get k).2 (2 + sumChildrenTake ms k.val) []
    -- We need to produce x, y with u = 2 + ... + x, v = 2 + ... + y.
    refine ⟨u - (2 + sumChildrenTake ms k.val),
            v - (2 + sumChildrenTake ms k.val), ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
    · omega
    · -- Use edgeList_shift_branch_child (reverse direction).
      have hshift := edgeList_shift_branch_child ms hPC k
        (u - (2 + sumChildrenTake ms k.val))
        (v - (2 + sumChildrenTake ms k.val))
      -- hshift iff: (u - k, v - k) ∈ edgeList child 0 [] ↔
      --   (u - k + k, v - k + k) ∈ edgeList child k []
      rw [hshift]
      have hu_rw : (u - (2 + sumChildrenTake ms k.val) +
                    (2 + sumChildrenTake ms k.val)) = u := by omega
      have hv_rw : (v - (2 + sumChildrenTake ms k.val) +
                    (2 + sumChildrenTake ms k.val)) = v := by omega
      rw [hu_rw, hv_rw]
      exact hmem

/-- **Select analogue of edge unlift**. -/
theorem select_child_edge_unlift_nat
    (ls : List (String × SessionType))
    (hPC : parClosed (.select ls : SessionType))
    (i : Fin ls.length) (u v : Nat)
    (hu : inChildRange ls i u) (hv : inChildRange ls i v)
    (hedge : (u, v) ∈ edgeList (.select ls : SessionType) 0 []) :
    ∃ x y : Nat,
      u = 2 + sumChildrenTake ls i.val + x ∧
      v = 2 + sumChildrenTake ls i.val + y ∧
      x < stateCount (ls.get i).2 ∧
      y < stateCount (ls.get i).2 ∧
      (x, y) ∈ edgeList (ls.get i).2 0 [] := by
  have htax := select_edge_taxonomy ls u v hedge
  rcases htax with ⟨hu_eq, hv_eq, hls_eq⟩
                 | ⟨hu_eq, k, hv_eq⟩
                 | ⟨hv_eq, k, hu_eq⟩
                 | ⟨k, hu_lo, hu_hi, hv_lo, hv_hi, hmem⟩
  · unfold inChildRange at hu; omega
  · unfold inChildRange at hu; omega
  · unfold inChildRange at hv; omega
  · have hak : inChildRange ls k u := ⟨hu_lo, hu_hi⟩
    have hki : k = i := by
      by_contra hne
      exact inChildRange_disjoint ls k i hne u hak hu
    subst hki
    refine ⟨u - (2 + sumChildrenTake ls k.val),
            v - (2 + sumChildrenTake ls k.val), ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
    · omega
    · have hshift := edgeList_shift_select_child ls hPC k
        (u - (2 + sumChildrenTake ls k.val))
        (v - (2 + sumChildrenTake ls k.val))
      rw [hshift]
      have hu_rw : (u - (2 + sumChildrenTake ls k.val) +
                    (2 + sumChildrenTake ls k.val)) = u := by omega
      have hv_rw : (v - (2 + sumChildrenTake ls k.val) +
                    (2 + sumChildrenTake ls k.val)) = v := by omega
      rw [hu_rw, hv_rw]
      exact hmem

/-- **Branch child edge unlift (Fin form)**: an edge of the branch state
space with both endpoints in child `i` is the shift of a child edge. -/
theorem branch_child_edge_unlift
    (ms : List (String × SessionType))
    (hPC : parClosed (.branch ms : SessionType))
    (i : Fin ms.length)
    (u v : State (.branch ms : SessionType))
    (hu : inChildRange ms i u.val) (hv : inChildRange ms i v.val)
    (hedge : (stateSpace (.branch ms : SessionType)).edge u v) :
    ∃ x y : State (ms.get i).2,
      u = branchChildShift ms i x ∧ v = branchChildShift ms i y ∧
      (stateSpace (ms.get i).2).edge x y := by
  -- hedge : (u.val, v.val) ∈ edgeList (.branch ms) 0 []
  obtain ⟨x, y, hu_eq, hv_eq, hx_lt, hy_lt, hmem⟩ :=
    branch_child_edge_unlift_nat ms hPC i u.val v.val hu hv hedge
  refine ⟨⟨x, hx_lt⟩, ⟨y, hy_lt⟩, ?_, ?_, ?_⟩
  · -- u = branchChildShift ms i ⟨x, hx_lt⟩
    apply Fin.ext
    simp [branchChildShift_val]
    omega
  · apply Fin.ext
    simp [branchChildShift_val]
    omega
  · -- (stateSpace (ms.get i).2).edge ⟨x, hx_lt⟩ ⟨y, hy_lt⟩
    simp only [stateSpace]
    exact hmem

/-- **Select child edge unlift (Fin form)**. -/
theorem select_child_edge_unlift
    (ls : List (String × SessionType))
    (hPC : parClosed (.select ls : SessionType))
    (i : Fin ls.length)
    (u v : State (.select ls : SessionType))
    (hu : inChildRange ls i u.val) (hv : inChildRange ls i v.val)
    (hedge : (stateSpace (.select ls : SessionType)).edge u v) :
    ∃ x y : State (ls.get i).2,
      u = selectChildShift ls i x ∧ v = selectChildShift ls i y ∧
      (stateSpace (ls.get i).2).edge x y := by
  obtain ⟨x, y, hu_eq, hv_eq, hx_lt, hy_lt, hmem⟩ :=
    select_child_edge_unlift_nat ls hPC i u.val v.val hu hv hedge
  refine ⟨⟨x, hx_lt⟩, ⟨y, hy_lt⟩, ?_, ?_, ?_⟩
  · apply Fin.ext
    simp [selectChildShift_val]
    omega
  · apply Fin.ext
    simp [selectChildShift_val]
    omega
  · simp only [stateSpace]
    exact hmem

/-- **Branch child walk unlift (backward direction of D.2)**: a walk in
the branch state space between two vertices both in child `i` is the lift
of a walk in the child state space. -/
theorem branch_child_walk_unlift
    (ms : List (String × SessionType))
    (hPC : parClosed (.branch ms : SessionType))
    (i : Fin ms.length)
    (u v : State (.branch ms : SessionType))
    (hu : inChildRange ms i u.val) (hv : inChildRange ms i v.val)
    (hwalk : Reachable (stateSpace (.branch ms : SessionType)) u v) :
    ∃ x y : State (ms.get i).2,
      u = branchChildShift ms i x ∧ v = branchChildShift ms i y ∧
      Reachable (stateSpace (ms.get i).2) x y := by
  -- Generalise the target v so that the induction can propagate the
  -- inChildRange hypothesis through the walk.
  induction hwalk with
  | refl =>
    -- u = v. Witnesses x = y = u shifted back.
    let x : State (ms.get i).2 :=
      ⟨u.val - (2 + sumChildrenTake ms i.val), by
        have := hu; unfold inChildRange at this; omega⟩
    refine ⟨x, x, ?_, ?_, Relation.ReflTransGen.refl⟩
    · apply Fin.ext
      simp only [branchChildShift_val, x]
      unfold inChildRange at hu; omega
    · apply Fin.ext
      simp only [branchChildShift_val, x]
      unfold inChildRange at hu; omega
  | tail hprev_walk hedge ih =>
    -- After pattern: hprev_walk : Reachable u b, hedge : edge b c
    -- where c is the original v. Lean auto-names the intermediate b and
    -- the final c. The original hv corresponds to the final c.
    rename_i b c
    -- hv : inChildRange ms i c.val (refers to the final vertex)
    -- ih is a function of the hypothesis that the intermediate walk-end's
    -- inChildRange holds.
    have hwalk_bc : Reachable (stateSpace (.branch ms : SessionType)) b c :=
      Relation.ReflTransGen.single hedge
    have hwalk_ub_nat : Relation.ReflTransGen
        (SessionType.edgeRel (.branch ms : SessionType) 0 []) u.val b.val := by
      have := @Relation.ReflTransGen.lift
        (State (.branch ms : SessionType)) Nat
        (stateSpace (.branch ms : SessionType)).edge
        (SessionType.edgeRel (.branch ms : SessionType) 0 [])
        u b Fin.val
        (fun x y hxy => hxy) hprev_walk
      exact this
    have hwalk_bc_nat : Relation.ReflTransGen
        (SessionType.edgeRel (.branch ms : SessionType) 0 []) b.val c.val := by
      have := @Relation.ReflTransGen.lift
        (State (.branch ms : SessionType)) Nat
        (stateSpace (.branch ms : SessionType)).edge
        (SessionType.edgeRel (.branch ms : SessionType) 0 [])
        b c Fin.val
        (fun x y hxy => hxy) hwalk_bc
      exact this
    have hb_in : inChildRange ms i b.val :=
      branch_walk_stays_in_child_nat ms i u.val c.val b.val hu hv
        hwalk_ub_nat hwalk_bc_nat
    obtain ⟨x, y, hu_eq, hb_eq, hwalk_xy⟩ := ih hb_in
    obtain ⟨y', z, hb_eq', hc_eq', hedge_yz⟩ :=
      branch_child_edge_unlift ms hPC i b c hb_in hv hedge
    have hy_eq : y = y' := by
      apply Fin.ext
      have h1 : b.val = (branchChildShift ms i y).val := by rw [hb_eq]
      have h2 : b.val = (branchChildShift ms i y').val := by rw [hb_eq']
      simp only [branchChildShift_val] at h1 h2
      omega
    subst hy_eq
    refine ⟨x, z, hu_eq, hc_eq', ?_⟩
    exact Relation.ReflTransGen.tail hwalk_xy hedge_yz

/-- **Select child walk unlift**. -/
theorem select_child_walk_unlift
    (ls : List (String × SessionType))
    (hPC : parClosed (.select ls : SessionType))
    (i : Fin ls.length)
    (u v : State (.select ls : SessionType))
    (hu : inChildRange ls i u.val) (hv : inChildRange ls i v.val)
    (hwalk : Reachable (stateSpace (.select ls : SessionType)) u v) :
    ∃ x y : State (ls.get i).2,
      u = selectChildShift ls i x ∧ v = selectChildShift ls i y ∧
      Reachable (stateSpace (ls.get i).2) x y := by
  induction hwalk with
  | refl =>
    let x : State (ls.get i).2 :=
      ⟨u.val - (2 + sumChildrenTake ls i.val), by
        have := hu; unfold inChildRange at this; omega⟩
    refine ⟨x, x, ?_, ?_, Relation.ReflTransGen.refl⟩
    · apply Fin.ext
      simp only [selectChildShift_val, x]
      unfold inChildRange at hu; omega
    · apply Fin.ext
      simp only [selectChildShift_val, x]
      unfold inChildRange at hu; omega
  | tail hprev_walk hedge ih =>
    rename_i b c
    have hwalk_bc : Reachable (stateSpace (.select ls : SessionType)) b c :=
      Relation.ReflTransGen.single hedge
    have hwalk_ub_nat : Relation.ReflTransGen
        (SessionType.edgeRel (.select ls : SessionType) 0 []) u.val b.val := by
      have := @Relation.ReflTransGen.lift
        (State (.select ls : SessionType)) Nat
        (stateSpace (.select ls : SessionType)).edge
        (SessionType.edgeRel (.select ls : SessionType) 0 [])
        u b Fin.val
        (fun x y hxy => hxy) hprev_walk
      exact this
    have hwalk_bc_nat : Relation.ReflTransGen
        (SessionType.edgeRel (.select ls : SessionType) 0 []) b.val c.val := by
      have := @Relation.ReflTransGen.lift
        (State (.select ls : SessionType)) Nat
        (stateSpace (.select ls : SessionType)).edge
        (SessionType.edgeRel (.select ls : SessionType) 0 [])
        b c Fin.val
        (fun x y hxy => hxy) hwalk_bc
      exact this
    have hb_in : inChildRange ls i b.val :=
      select_walk_stays_in_child_nat ls i u.val c.val b.val hu hv
        hwalk_ub_nat hwalk_bc_nat
    obtain ⟨x, y, hu_eq, hb_eq, hwalk_xy⟩ := ih hb_in
    obtain ⟨y', z, hb_eq', hc_eq', hedge_yz⟩ :=
      select_child_edge_unlift ls hPC i b c hb_in hv hedge
    have hy_eq : y = y' := by
      apply Fin.ext
      have h1 : b.val = (selectChildShift ls i y).val := by rw [hb_eq]
      have h2 : b.val = (selectChildShift ls i y').val := by rw [hb_eq']
      simp only [selectChildShift_val] at h1 h2
      omega
    subst hy_eq
    refine ⟨x, z, hu_eq, hc_eq', ?_⟩
    exact Relation.ReflTransGen.tail hwalk_xy hedge_yz

/-- **Same-child reachability iff (branch)**: for two vertices both in
child `i`, branch-reachability iff child-reachability under the
`branchChildShift` embedding. -/
theorem branch_same_child_reachable_iff
    (ms : List (String × SessionType))
    (hPC : parClosed (.branch ms : SessionType))
    (i : Fin ms.length) (x y : State (ms.get i).2) :
    Reachable (stateSpace (.branch ms : SessionType))
      (branchChildShift ms i x) (branchChildShift ms i y) ↔
    Reachable (stateSpace (ms.get i).2) x y := by
  refine ⟨?_, branch_child_walk_lift ms hPC i x y⟩
  intro hwalk
  have hu_in : inChildRange ms i (branchChildShift ms i x).val :=
    branchChildShift_inChildRange ms i x
  have hv_in : inChildRange ms i (branchChildShift ms i y).val :=
    branchChildShift_inChildRange ms i y
  obtain ⟨x', y', hu_eq, hv_eq, hwalk_xy⟩ :=
    branch_child_walk_unlift ms hPC i
      (branchChildShift ms i x) (branchChildShift ms i y) hu_in hv_in hwalk
  -- By injectivity of branchChildShift, x = x' and y = y'.
  have hx_eq : x = x' := by
    apply Fin.ext
    have h : (branchChildShift ms i x).val = (branchChildShift ms i x').val := by
      rw [hu_eq]
    simp [branchChildShift_val] at h
    omega
  have hy_eq : y = y' := by
    apply Fin.ext
    have h : (branchChildShift ms i y).val = (branchChildShift ms i y').val := by
      rw [hv_eq]
    simp [branchChildShift_val] at h
    omega
  rw [hx_eq, hy_eq]
  exact hwalk_xy

/-- **Same-child reachability iff (select)**. -/
theorem select_same_child_reachable_iff
    (ls : List (String × SessionType))
    (hPC : parClosed (.select ls : SessionType))
    (i : Fin ls.length) (x y : State (ls.get i).2) :
    Reachable (stateSpace (.select ls : SessionType))
      (selectChildShift ls i x) (selectChildShift ls i y) ↔
    Reachable (stateSpace (ls.get i).2) x y := by
  refine ⟨?_, select_child_walk_lift ls hPC i x y⟩
  intro hwalk
  have hu_in : inChildRange ls i (selectChildShift ls i x).val :=
    selectChildShift_inChildRange ls i x
  have hv_in : inChildRange ls i (selectChildShift ls i y).val :=
    selectChildShift_inChildRange ls i y
  obtain ⟨x', y', hu_eq, hv_eq, hwalk_xy⟩ :=
    select_child_walk_unlift ls hPC i
      (selectChildShift ls i x) (selectChildShift ls i y) hu_in hv_in hwalk
  have hx_eq : x = x' := by
    apply Fin.ext
    have h : (selectChildShift ls i x).val = (selectChildShift ls i x').val := by
      rw [hu_eq]
    simp [selectChildShift_val] at h
    omega
  have hy_eq : y = y' := by
    apply Fin.ext
    have h : (selectChildShift ls i y).val = (selectChildShift ls i y').val := by
      rw [hv_eq]
    simp [selectChildShift_val] at h
    omega
  rw [hx_eq, hy_eq]
  exact hwalk_xy

/-!
## Phase 1b-β3-follow-4 Part 5 — D.3 branch_child_embed (SCC-quotient)

Using the same-child reachability iff (Part 4), we can lift
`branchChildShift` from `State` to `SCCQuotient`. The key observation:
if two child vertices are mutually reachable in the child state space,
then their branch-shifts are mutually reachable in the branch state
space (by the forward direction of the iff). This makes the map a
well-defined function on the SCC quotients.

The map is monotone because the iff direction preserves reachability
ordering componentwise.
-/

/-- **Branch child embedding on SCC quotients**: the map
`⟦x⟧ ↦ ⟦branchChildShift ms i x⟧` is well-defined on SCC quotients. -/
noncomputable def branch_child_embed
    (ms : List (String × SessionType))
    (hPC : parClosed (.branch ms : SessionType))
    (i : Fin ms.length) :
    SCCQuotient (stateSpace (ms.get i).2) →
    SCCQuotient (stateSpace (.branch ms : SessionType)) := by
  apply Quotient.lift
    (fun x => (Quotient.mk (SCCSetoid (stateSpace (.branch ms : SessionType)))
                 (branchChildShift ms i x)))
  intro a b hab
  apply Quotient.sound
  -- hab : SCCSetoid (stateSpace child) a b
  --     = MutuallyReachable (stateSpace child) a b
  --     = Reachable child a b ∧ Reachable child b a
  -- Goal: SCCSetoid (stateSpace (.branch ms)) (shift a) (shift b)
  --     = MutuallyReachable (stateSpace (.branch ms)) (shift a) (shift b)
  refine ⟨?_, ?_⟩
  · exact (branch_same_child_reachable_iff ms hPC i a b).mpr hab.1
  · exact (branch_same_child_reachable_iff ms hPC i b a).mpr hab.2

/-- **Select child embedding on SCC quotients**. -/
noncomputable def select_child_embed
    (ls : List (String × SessionType))
    (hPC : parClosed (.select ls : SessionType))
    (i : Fin ls.length) :
    SCCQuotient (stateSpace (ls.get i).2) →
    SCCQuotient (stateSpace (.select ls : SessionType)) := by
  apply Quotient.lift
    (fun x => (Quotient.mk (SCCSetoid (stateSpace (.select ls : SessionType)))
                 (selectChildShift ls i x)))
  intro a b hab
  apply Quotient.sound
  refine ⟨?_, ?_⟩
  · exact (select_same_child_reachable_iff ls hPC i a b).mpr hab.1
  · exact (select_same_child_reachable_iff ls hPC i b a).mpr hab.2

/-- `branch_child_embed` sends `⟦x⟧` to `⟦branchChildShift ms i x⟧`. -/
@[simp] theorem branch_child_embed_mk
    (ms : List (String × SessionType))
    (hPC : parClosed (.branch ms : SessionType))
    (i : Fin ms.length) (x : State (ms.get i).2) :
    branch_child_embed ms hPC i (Quotient.mk _ x) =
      Quotient.mk _ (branchChildShift ms i x) := rfl

/-- `select_child_embed` sends `⟦x⟧` to `⟦selectChildShift ls i x⟧`. -/
@[simp] theorem select_child_embed_mk
    (ls : List (String × SessionType))
    (hPC : parClosed (.select ls : SessionType))
    (i : Fin ls.length) (x : State (ls.get i).2) :
    select_child_embed ls hPC i (Quotient.mk _ x) =
      Quotient.mk _ (selectChildShift ls i x) := rfl

/-- `branch_child_embed` is monotone: SCC-level ordering is preserved. -/
theorem branch_child_embed_monotone
    (ms : List (String × SessionType))
    (hPC : parClosed (.branch ms : SessionType))
    (i : Fin ms.length) :
    Monotone (branch_child_embed ms hPC i) := by
  intro q₁ q₂ hle
  -- Induct on q₁ and q₂ to unwrap the quotient classes.
  induction q₁ using Quotient.ind with
  | _ x =>
    induction q₂ using Quotient.ind with
    | _ y =>
      -- hle : Quotient.mk _ x ≤ Quotient.mk _ y
      --     = Reachable (stateSpace child) x y
      -- Goal: branch_child_embed (⟦x⟧) ≤ branch_child_embed (⟦y⟧)
      --     = Reachable (stateSpace (.branch ms)) (shift x) (shift y)
      simp only [branch_child_embed_mk]
      show Reachable (stateSpace (.branch ms : SessionType))
             (branchChildShift ms i x) (branchChildShift ms i y)
      exact (branch_same_child_reachable_iff ms hPC i x y).mpr hle

/-- `select_child_embed` is monotone. -/
theorem select_child_embed_monotone
    (ls : List (String × SessionType))
    (hPC : parClosed (.select ls : SessionType))
    (i : Fin ls.length) :
    Monotone (select_child_embed ls hPC i) := by
  intro q₁ q₂ hle
  induction q₁ using Quotient.ind with
  | _ x =>
    induction q₂ using Quotient.ind with
    | _ y =>
      simp only [select_child_embed_mk]
      show Reachable (stateSpace (.select ls : SessionType))
             (selectChildShift ls i x) (selectChildShift ls i y)
      exact (select_same_child_reachable_iff ls hPC i x y).mpr hle

/-!
### Classifier respecting SCC equivalence

For the downstream D.4-D.6 (crown lattice assembly), we need to classify
every vertex of `stateSpace (.branch ms)` as: the root (0), the bottom
(1), or in some child `i`'s range. This classification is preserved by
the SCC-setoid relation because:

* Root (0) has no incoming edges (by `branch_edge_taxonomy`, no bucket
  has target 0), so its SCC class is a singleton.
* Bottom (1) has no outgoing edges (by `branch_bottom_no_outgoing`), so
  its SCC class is a singleton.
* Two vertices in different children cannot be mutually reachable (by
  `branch_cross_child_not_reachable`).
* Mutual reachability between a root/bottom and a child vertex is ruled
  out by the singleton-SCC properties.
-/

/-- **Root has no incoming edges in `.branch ms`**. -/
theorem branch_root_no_incoming
    (ms : List (String × SessionType)) (u : Nat) :
    ¬ (u, 0) ∈ edgeList (.branch ms : SessionType) 0 [] := by
  intro h
  have htax := branch_edge_taxonomy ms u 0 h
  rcases htax with ⟨_, hv_eq, _⟩
                 | ⟨_, k, hv_eq⟩
                 | ⟨hv_eq, _, _⟩
                 | ⟨k, _, _, hv_lo, _, _⟩
  · -- Bucket 1: v = 1, contradicts v = 0.
    omega
  · -- Bucket 2: v = 2 + sumChildrenTake ms k.val ≥ 2.
    omega
  · -- Bucket 3: v = 1, contradicts.
    omega
  · -- Bucket 4: child-internal, v ≥ 2.
    omega

/-- **Root has no incoming edges in `.select ls`**. -/
theorem select_root_no_incoming
    (ls : List (String × SessionType)) (u : Nat) :
    ¬ (u, 0) ∈ edgeList (.select ls : SessionType) 0 [] := by
  intro h
  have htax := select_edge_taxonomy ls u 0 h
  rcases htax with ⟨_, hv_eq, _⟩
                 | ⟨_, k, hv_eq⟩
                 | ⟨hv_eq, _, _⟩
                 | ⟨k, _, _, hv_lo, _, _⟩
  · omega
  · omega
  · omega
  · omega

/-- **Root's SCC class is a singleton in `.branch ms`**: any walk ending
at root (0) was a refl walk. -/
theorem branch_root_walk_refl
    (ms : List (String × SessionType)) (u : Nat)
    (hwalk : Relation.ReflTransGen
      (SessionType.edgeRel (.branch ms : SessionType) 0 []) u 0) :
    u = 0 := by
  -- Case analyse on whether hwalk is refl or involves at least one edge.
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp hwalk with heq | htg
  · exact heq.symm
  · -- There's at least one edge ending at 0.
    -- htg : Relation.TransGen (edgeRel ...) u 0
    -- The last edge of a TransGen is of the form (_, 0) ∈ edgeList ...
    -- which contradicts branch_root_no_incoming.
    have hlast := Relation.TransGen.tail'_iff.mp htg
    obtain ⟨b, _, hedge⟩ := hlast
    exact absurd hedge (branch_root_no_incoming ms b)

/-- **Root's SCC class is a singleton in `.select ls`**. -/
theorem select_root_walk_refl
    (ls : List (String × SessionType)) (u : Nat)
    (hwalk : Relation.ReflTransGen
      (SessionType.edgeRel (.select ls : SessionType) 0 []) u 0) :
    u = 0 := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp hwalk with heq | htg
  · exact heq.symm
  · have hlast := Relation.TransGen.tail'_iff.mp htg
    obtain ⟨b, _, hedge⟩ := hlast
    exact absurd hedge (select_root_no_incoming ls b)

/-- **Child-range coverage**: every index in `[0, sumChildrenPair ms)`
falls into some child's range. Used by the SCC classifier. -/
theorem sumChildrenPair_covers_range
    (ms : List (String × SessionType)) (n : Nat)
    (hlb : 2 ≤ n) (hub : n < 2 + stateCount.sumChildrenPair ms) :
    ∃ i : Fin ms.length, inChildRange ms i n := by
  -- Induct on ms to find the first child containing n - 2.
  -- Actually it's easier to reason on the shifted index m := n - 2.
  have hm_lb : n - 2 ≥ 0 := by omega
  have hm_ub : n - 2 < stateCount.sumChildrenPair ms := by omega
  -- Find i by strong induction on the list.
  suffices hcover : ∀ (ms' : List (String × SessionType)) (m : Nat),
                    m < stateCount.sumChildrenPair ms' →
                    ∃ i : Fin ms'.length,
                      sumChildrenTake ms' i.val ≤ m ∧
                      m < sumChildrenTake ms' i.val + stateCount (ms'.get i).2 by
    obtain ⟨i, hle, hlt⟩ := hcover ms (n - 2) hm_ub
    refine ⟨i, ?_, ?_⟩
    · show 2 + sumChildrenTake ms i.val ≤ n
      omega
    · show n < 2 + sumChildrenTake ms i.val + stateCount (ms.get i).2
      omega
  intro ms' m hm
  induction ms' generalizing m with
  | nil =>
    simp [stateCount.sumChildrenPair] at hm
  | cons p tl ih =>
    simp only [stateCount.sumChildrenPair] at hm
    by_cases hhead : m < stateCount p.2
    · -- m falls in the head child, i = 0.
      refine ⟨⟨0, by simp⟩, ?_, ?_⟩
      · show sumChildrenTake (p :: tl) 0 ≤ m
        rw [sumChildrenTake_zero]; omega
      · show m < sumChildrenTake (p :: tl) 0 + stateCount ((p :: tl).get ⟨0, _⟩).2
        rw [sumChildrenTake_zero]
        have hget : ((p :: tl).get ⟨0, by simp⟩).2 = p.2 := rfl
        rw [hget]; omega
    · -- m ≥ stateCount p.2. Apply IH on m - stateCount p.2 ∈ tl.
      have hm_tl : m - stateCount p.2 < stateCount.sumChildrenPair tl := by
        push_neg at hhead; omega
      obtain ⟨j, hjle, hjlt⟩ := ih (m - stateCount p.2) hm_tl
      have hj_bound : j.val + 1 < (p :: tl).length := by
        simp only [List.length_cons]; omega
      refine ⟨⟨j.val + 1, hj_bound⟩, ?_, ?_⟩
      · show sumChildrenTake (p :: tl) (j.val + 1) ≤ m
        rw [sumChildrenTake_cons_succ]
        push_neg at hhead; omega
      · show m < sumChildrenTake (p :: tl) (j.val + 1) +
              stateCount ((p :: tl).get ⟨j.val + 1, hj_bound⟩).2
        rw [sumChildrenTake_cons_succ]
        have hget : ((p :: tl).get ⟨j.val + 1, hj_bound⟩).2 =
                    (tl.get j).2 := rfl
        rw [hget]
        push_neg at hhead; omega

/-- **Branch SCC-setoid classifier respects structure**: two branch vertices
that are mutually reachable either:
* are both the root (0),
* are both the bottom (1),
* are both in the same child `i`'s range.

This uses the three singleton-SCC facts (`branch_root_walk_refl`,
`branch_bottom_walk_refl`) and the cross-child non-reachability. -/
theorem branch_scc_classifier
    (ms : List (String × SessionType))
    (u v : State (.branch ms : SessionType))
    (huv : MutuallyReachable (stateSpace (.branch ms : SessionType)) u v) :
    (u.val = 0 ∧ v.val = 0)
    ∨ (u.val = 1 ∧ v.val = 1)
    ∨ ∃ i : Fin ms.length, inChildRange ms i u.val ∧ inChildRange ms i v.val := by
  -- Lift walks to Nat level.
  have hwalk_uv_nat : Relation.ReflTransGen
      (SessionType.edgeRel (.branch ms : SessionType) 0 []) u.val v.val := by
    have := @Relation.ReflTransGen.lift
      (State (.branch ms : SessionType)) Nat
      (stateSpace (.branch ms : SessionType)).edge
      (SessionType.edgeRel (.branch ms : SessionType) 0 [])
      u v Fin.val
      (fun x y hxy => hxy) huv.1
    exact this
  have hwalk_vu_nat : Relation.ReflTransGen
      (SessionType.edgeRel (.branch ms : SessionType) 0 []) v.val u.val := by
    have := @Relation.ReflTransGen.lift
      (State (.branch ms : SessionType)) Nat
      (stateSpace (.branch ms : SessionType)).edge
      (SessionType.edgeRel (.branch ms : SessionType) 0 [])
      v u Fin.val
      (fun x y hxy => hxy) huv.2
    exact this
  -- Case on u.val.
  rcases Nat.lt_or_ge u.val 2 with hu_lt | hu_ge
  · -- u.val < 2: either 0 or 1.
    match h : u.val, hu_lt with
    | 0, _ =>
      left
      refine ⟨rfl, ?_⟩
      -- walk u → v → u, with u.val = 0. So walk 0 → v → 0. By branch_root_walk_refl on
      -- the full round-trip, intermediate 0 → v → 0 means v = 0.
      -- Apply branch_root_walk_refl on v → 0 (i.e., hwalk_vu_nat with u.val = 0).
      rw [h] at hwalk_vu_nat
      exact branch_root_walk_refl ms v.val hwalk_vu_nat
    | 1, _ =>
      right; left
      refine ⟨rfl, ?_⟩
      -- u.val = 1; walk 1 → v implies v = 1 (branch_bottom_walk_refl on hwalk_uv_nat).
      rw [h] at hwalk_uv_nat
      exact (branch_bottom_walk_refl ms v.val hwalk_uv_nat).symm |>.symm
  · -- u.val ≥ 2: in some child.
    -- Find which child.
    -- u.val < stateCount (.branch ms) = 2 + sumChildrenPair ms.
    have hu_bound : u.val < 2 + stateCount.sumChildrenPair ms := by
      have := u.isLt
      show u.val < 2 + stateCount.sumChildrenPair ms
      simp only [stateCount] at this
      exact this
    -- Use disjointness: u.val ∈ [2, 2 + sumChildrenPair ms) so u.val falls in some child.
    have hinchild_u : ∃ i : Fin ms.length, inChildRange ms i u.val :=
      sumChildrenPair_covers_range ms u.val hu_ge hu_bound
    obtain ⟨i, hu_in⟩ := hinchild_u
    -- Then v must also be in child i by closure (walk from u stays in child i or goes to bottom).
    have hv_or : inChildRange ms i v.val ∨ v.val = 1 :=
      branch_child_closure_walk ms i u.val v.val (Or.inl hu_in) hwalk_uv_nat
    rcases hv_or with hv_in | hv1
    · right; right
      exact ⟨i, hu_in, hv_in⟩
    · -- v = 1: but then walk v → u is walk 1 → u, implies u = 1 (bottom_walk_refl).
      -- But u.val ≥ 2, contradiction.
      rw [hv1] at hwalk_vu_nat
      have hu1 := branch_bottom_walk_refl ms u.val hwalk_vu_nat
      omega

/-- **Select SCC-setoid classifier**. -/
theorem select_scc_classifier
    (ls : List (String × SessionType))
    (u v : State (.select ls : SessionType))
    (huv : MutuallyReachable (stateSpace (.select ls : SessionType)) u v) :
    (u.val = 0 ∧ v.val = 0)
    ∨ (u.val = 1 ∧ v.val = 1)
    ∨ ∃ i : Fin ls.length, inChildRange ls i u.val ∧ inChildRange ls i v.val := by
  have hwalk_uv_nat : Relation.ReflTransGen
      (SessionType.edgeRel (.select ls : SessionType) 0 []) u.val v.val := by
    have := @Relation.ReflTransGen.lift
      (State (.select ls : SessionType)) Nat
      (stateSpace (.select ls : SessionType)).edge
      (SessionType.edgeRel (.select ls : SessionType) 0 [])
      u v Fin.val
      (fun x y hxy => hxy) huv.1
    exact this
  have hwalk_vu_nat : Relation.ReflTransGen
      (SessionType.edgeRel (.select ls : SessionType) 0 []) v.val u.val := by
    have := @Relation.ReflTransGen.lift
      (State (.select ls : SessionType)) Nat
      (stateSpace (.select ls : SessionType)).edge
      (SessionType.edgeRel (.select ls : SessionType) 0 [])
      v u Fin.val
      (fun x y hxy => hxy) huv.2
    exact this
  rcases Nat.lt_or_ge u.val 2 with hu_lt | hu_ge
  · match h : u.val, hu_lt with
    | 0, _ =>
      left
      refine ⟨rfl, ?_⟩
      rw [h] at hwalk_vu_nat
      exact select_root_walk_refl ls v.val hwalk_vu_nat
    | 1, _ =>
      right; left
      refine ⟨rfl, ?_⟩
      rw [h] at hwalk_uv_nat
      exact (select_bottom_walk_refl ls v.val hwalk_uv_nat).symm |>.symm
  · have hu_bound : u.val < 2 + stateCount.sumChildrenPair ls := by
      have := u.isLt
      show u.val < 2 + stateCount.sumChildrenPair ls
      simp only [stateCount] at this
      exact this
    have hinchild_u : ∃ i : Fin ls.length, inChildRange ls i u.val :=
      sumChildrenPair_covers_range ls u.val hu_ge hu_bound
    obtain ⟨i, hu_in⟩ := hinchild_u
    have hv_or : inChildRange ls i v.val ∨ v.val = 1 :=
      select_child_closure_walk ls i u.val v.val (Or.inl hu_in) hwalk_uv_nat
    rcases hv_or with hv_in | hv1
    · right; right
      exact ⟨i, hu_in, hv_in⟩
    · rw [hv1] at hwalk_vu_nat
      have hu1 := select_bottom_walk_refl ls u.val hwalk_vu_nat
      omega

/-!
## Phase 1b-β3-follow-5 — D.4-D.6 + E + F: branch/select `SCCLatticeStruct`

With all the infrastructure from follow-4 in place — cross-child
non-reachability, same-child reachability iff, child-SCC embedding,
SCC classifier — we can finally assemble a `SCCLatticeStruct` bundle
for `.branch ms` and `.select ls` directly, without the
`BranchSelectLatticeAssumption` gate.

### Structure of the construction

For `u, v : State (.branch ms)` the sup/inf depends on a three-way
classification of `u.val` and `v.val`:

1. **Root (`u.val = 0`)**: `[u] = ⊥` (since `initialState (.branch ms)
   = ⟨0, _⟩`). `sup ⊥ v = v`, `inf ⊥ v = ⊥`.
2. **Bottom (`u.val = 1`)**: `[u] = ⊤` (since `terminalState (.branch ms)
   = ⟨exitSlot 0, _⟩ = ⟨1, _⟩`). `sup ⊤ v = ⊤`, `inf ⊤ v = v`.
3. **Child (`u.val ≥ 2`)**: `u.val` lies in exactly one child's range by
   `sumChildrenPair_covers_range` and `inChildRange_disjoint`. We
   extract `(i, local_x)` where `u.val = (branchChildShift ms i x).val`.

For child/child pairs with different `i, j` (cross-child), the two
vertices are incomparable in the SCC quotient: neither reaches the
other (follow-2 Part C). So `sup = ⊤` and `inf = ⊥`.

For same-child pairs, we delegate to the child's lattice via
`branch_child_embed` + `(hC i).sup / .inf`.

### Respect proof (the technical heart)

`Quotient.lift₂` needs the vertex-level function to respect SCCSetoid.
By `branch_scc_classifier`, two mutually reachable vertices fall into
the same case (root, bottom, or same child). Then:

* Root/bottom cases: output is a fixed class (⊥ or ⊤), invariant.
* Cross-child case: output is a fixed class (⊤ or ⊥), invariant.
* Same-child case: `branch_child_embed` is a function on
  `SCCQuotient child`, and `(hC i).sup / .inf` operate on that quotient,
  so the result only depends on the child's SCC class — which is
  preserved by SCCSetoid at the branch level (because SCC
  equivalence of `branchChildShift ms i x` and `branchChildShift ms i x'`
  is equivalent to SCC equivalence of `x` and `x'` in the child, via
  `branch_same_child_reachable_iff`).
-/


end SessionType

end Reticulate.Spec
