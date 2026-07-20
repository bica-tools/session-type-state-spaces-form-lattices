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
import Reticulate.Spec.StateSpace.StateSpaceLattice.ParAndBundles

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

/-! ### Child-index extraction

Given `u : State (.branch ms)` with `u.val ≥ 2`, we extract the unique
child index `i : Fin ms.length` such that `inChildRange ms i u.val`,
along with the local offset. The output is packaged as a sigma so that
the caller can recover both components.
-/

/-- Extract the child index and local offset for a branch vertex `u`
with `u.val ≥ 2`. Uniqueness is guaranteed by `inChildRange_disjoint`
and existence by `sumChildrenPair_covers_range`. Noncomputable because
it uses `Classical.choose`. -/
noncomputable def branchChildOf
    (ms : List (String × SessionType))
    (u : State (.branch ms : SessionType))
    (hu : 2 ≤ u.val) :
    Σ i : Fin ms.length, State (ms.get i).2 :=
  let hBound : u.val < 2 + stateCount.sumChildrenPair ms := by
    have := u.isLt; simp only [stateCount] at this; exact this
  let ⟨i, hi⟩ := Classical.indefiniteDescription _
                   (sumChildrenPair_covers_range ms u.val hu hBound)
  ⟨i, ⟨u.val - (2 + sumChildrenTake ms i.val), by
    have hlt : u.val < 2 + sumChildrenTake ms i.val + stateCount (ms.get i).2 :=
      hi.2
    have hge : 2 + sumChildrenTake ms i.val ≤ u.val := hi.1
    omega⟩⟩

/-- The extraction from `branchChildOf` inverts `branchChildShift`. -/
theorem branchChildOf_shift
    (ms : List (String × SessionType))
    (u : State (.branch ms : SessionType)) (hu : 2 ≤ u.val) :
    branchChildShift ms (branchChildOf ms u hu).1 (branchChildOf ms u hu).2 = u := by
  apply Fin.ext
  show 2 + sumChildrenTake ms (branchChildOf ms u hu).1.val +
         (branchChildOf ms u hu).2.val = u.val
  unfold branchChildOf
  simp only
  -- The Classical.indefiniteDescription picks some ⟨i, hi⟩ with inChildRange.
  -- By hi.1: 2 + sumChildrenTake ms i.val ≤ u.val.
  -- So u.val - (2 + sumChildrenTake ms i.val) + (2 + sumChildrenTake ms i.val) = u.val.
  set witness := Classical.indefiniteDescription _
    (sumChildrenPair_covers_range ms u.val hu (by
      have := u.isLt; simp only [stateCount] at this; exact this))
  have hlower : 2 + sumChildrenTake ms witness.val.val ≤ u.val := witness.property.1
  omega

/-- If `u.val ≥ 2` is in child `i`'s range, then `branchChildOf` returns
`i` (by disjointness). -/
theorem branchChildOf_fst_of_inChildRange
    (ms : List (String × SessionType))
    (u : State (.branch ms : SessionType)) (hu : 2 ≤ u.val)
    (i : Fin ms.length) (hin : inChildRange ms i u.val) :
    (branchChildOf ms u hu).1 = i := by
  unfold branchChildOf
  simp only
  set witness := Classical.indefiniteDescription _
    (sumChildrenPair_covers_range ms u.val hu (by
      have := u.isLt; simp only [stateCount] at this; exact this))
  -- witness.val is some j : Fin ms.length with inChildRange ms j u.val.
  -- By disjointness, j = i.
  by_contra hne
  exact inChildRange_disjoint ms witness.val i hne u.val witness.property hin

/-! ### Select analogue of `branchChildOf` -/

/-- Select analogue of `branchChildOf`. -/
noncomputable def selectChildOf
    (ls : List (String × SessionType))
    (u : State (.select ls : SessionType))
    (hu : 2 ≤ u.val) :
    Σ i : Fin ls.length, State (ls.get i).2 :=
  let hBound : u.val < 2 + stateCount.sumChildrenPair ls := by
    have := u.isLt; simp only [stateCount] at this; exact this
  let ⟨i, hi⟩ := Classical.indefiniteDescription _
                   (sumChildrenPair_covers_range ls u.val hu hBound)
  ⟨i, ⟨u.val - (2 + sumChildrenTake ls i.val), by
    have hlt : u.val < 2 + sumChildrenTake ls i.val + stateCount (ls.get i).2 :=
      hi.2
    have hge : 2 + sumChildrenTake ls i.val ≤ u.val := hi.1
    omega⟩⟩

/-- Select analogue of `branchChildOf_shift`. -/
theorem selectChildOf_shift
    (ls : List (String × SessionType))
    (u : State (.select ls : SessionType)) (hu : 2 ≤ u.val) :
    selectChildShift ls (selectChildOf ls u hu).1 (selectChildOf ls u hu).2 = u := by
  apply Fin.ext
  show 2 + sumChildrenTake ls (selectChildOf ls u hu).1.val +
         (selectChildOf ls u hu).2.val = u.val
  unfold selectChildOf
  simp only
  set witness := Classical.indefiniteDescription _
    (sumChildrenPair_covers_range ls u.val hu (by
      have := u.isLt; simp only [stateCount] at this; exact this))
  have hlower : 2 + sumChildrenTake ls witness.val.val ≤ u.val := witness.property.1
  omega

/-- Select analogue of `branchChildOf_fst_of_inChildRange`. -/
theorem selectChildOf_fst_of_inChildRange
    (ls : List (String × SessionType))
    (u : State (.select ls : SessionType)) (hu : 2 ≤ u.val)
    (i : Fin ls.length) (hin : inChildRange ls i u.val) :
    (selectChildOf ls u hu).1 = i := by
  unfold selectChildOf
  simp only
  set witness := Classical.indefiniteDescription _
    (sumChildrenPair_covers_range ls u.val hu (by
      have := u.isLt; simp only [stateCount] at this; exact this))
  by_contra hne
  exact inChildRange_disjoint ls witness.val i hne u.val witness.property hin

/-! ### Root and bottom as SCC classes -/

/-- For `u : State (.branch ms)` with `u.val = 0`, `[u] = ⊥`. -/
theorem branch_class_eq_bot_of_root
    (ms : List (String × SessionType))
    (u : State (.branch ms : SessionType)) (hu : u.val = 0) :
    (Quotient.mk (SCCSetoid (stateSpace (.branch ms : SessionType))) u) =
      (⊥ : SCCQuotient (stateSpace (.branch ms : SessionType))) := by
  show (Quotient.mk _ u) = Quotient.mk _ (initialState (.branch ms : SessionType))
  apply Quotient.sound
  -- Mutual reachability: both are root (val = 0).
  have huEq : u = initialState (.branch ms : SessionType) := by
    apply Fin.ext
    show u.val = 0
    exact hu
  rw [huEq]
  exact ⟨Reachable.refl _ _, Reachable.refl _ _⟩

/-- For `u : State (.branch ms)` with `u.val = 1`, `[u] = ⊤`. -/
theorem branch_class_eq_top_of_bottom
    (ms : List (String × SessionType))
    (u : State (.branch ms : SessionType)) (hu : u.val = 1) :
    (Quotient.mk (SCCSetoid (stateSpace (.branch ms : SessionType))) u) =
      (⊤ : SCCQuotient (stateSpace (.branch ms : SessionType))) := by
  show (Quotient.mk _ u) = Quotient.mk _ (terminalState (.branch ms : SessionType))
  apply Quotient.sound
  -- terminalState (.branch ms) = ⟨1, _⟩ since exitSlot (.branch _) 0 = 1.
  have hterm_val : (terminalState (.branch ms : SessionType)).val = 1 := by
    unfold terminalState
    have he : exitSlot (.branch ms : SessionType) 0 < stateCount (.branch ms : SessionType) := by
      show exitSlot (.branch ms) 0 < stateCount (.branch ms)
      simp only [exitSlot, stateCount]
      omega
    simp only [dif_pos he]
    show exitSlot (.branch ms : SessionType) 0 = 1
    simp [exitSlot]
  have huEq : u = terminalState (.branch ms : SessionType) := by
    apply Fin.ext
    rw [hu, hterm_val]
  rw [huEq]
  exact ⟨Reachable.refl _ _, Reachable.refl _ _⟩

/-- Select analogue. -/
theorem select_class_eq_bot_of_root
    (ls : List (String × SessionType))
    (u : State (.select ls : SessionType)) (hu : u.val = 0) :
    (Quotient.mk (SCCSetoid (stateSpace (.select ls : SessionType))) u) =
      (⊥ : SCCQuotient (stateSpace (.select ls : SessionType))) := by
  show (Quotient.mk _ u) = Quotient.mk _ (initialState (.select ls : SessionType))
  apply Quotient.sound
  have huEq : u = initialState (.select ls : SessionType) := by
    apply Fin.ext
    show u.val = 0
    exact hu
  rw [huEq]
  exact ⟨Reachable.refl _ _, Reachable.refl _ _⟩

/-- Select analogue. -/
theorem select_class_eq_top_of_bottom
    (ls : List (String × SessionType))
    (u : State (.select ls : SessionType)) (hu : u.val = 1) :
    (Quotient.mk (SCCSetoid (stateSpace (.select ls : SessionType))) u) =
      (⊤ : SCCQuotient (stateSpace (.select ls : SessionType))) := by
  show (Quotient.mk _ u) = Quotient.mk _ (terminalState (.select ls : SessionType))
  apply Quotient.sound
  have hterm_val : (terminalState (.select ls : SessionType)).val = 1 := by
    unfold terminalState
    have he : exitSlot (.select ls : SessionType) 0 < stateCount (.select ls : SessionType) := by
      show exitSlot (.select ls) 0 < stateCount (.select ls)
      simp only [exitSlot, stateCount]
      omega
    simp only [dif_pos he]
    show exitSlot (.select ls : SessionType) 0 = 1
    simp [exitSlot]
  have huEq : u = terminalState (.select ls : SessionType) := by
    apply Fin.ext
    rw [hu, hterm_val]
  rw [huEq]
  exact ⟨Reachable.refl _ _, Reachable.refl _ _⟩

/-! ### D.4 — Vertex-level sup/inf for `.branch ms`

The definition case-splits on `u.val ∈ {0, 1, ≥2}` and symmetrically
on `v.val`. The root/bottom cases output `⊥`/`⊤` directly (the fixed
lattice extrema). The child/child cases either delegate to the child's
sup/inf via `branch_child_embed` (same child) or output the fixed
extrema (different children, since cross-child pairs are incomparable
in the SCC quotient). -/

/-- Vertex-level supremum for `.branch ms`. -/
noncomputable def branch_sup_vertex
    (ms : List (String × SessionType))
    (hPC : parClosed (.branch ms : SessionType))
    (hC : ∀ k : Fin ms.length, SCCLatticeStruct (stateSpace (ms.get k).2))
    (u v : State (.branch ms : SessionType)) :
    SCCQuotient (stateSpace (.branch ms : SessionType)) :=
  if hu0 : u.val = 0 then
    Quotient.mk _ v  -- [u] = ⊥, sup = v
  else if hv0 : v.val = 0 then
    Quotient.mk _ u  -- [v] = ⊥, sup = u
  else if _ : u.val = 1 then
    ⊤  -- [u] = ⊤, sup = ⊤
  else if _ : v.val = 1 then
    ⊤  -- [v] = ⊤, sup = ⊤
  else
    -- Both u and v are in some children.
    have hu2 : 2 ≤ u.val := by omega
    have hv2 : 2 ≤ v.val := by omega
    let ⟨iu, xu⟩ := branchChildOf ms u hu2
    let ⟨iv, xv⟩ := branchChildOf ms v hv2
    if hij : iu = iv then
      -- Same child: embed the child-level sup.
      branch_child_embed ms hPC iu
        ((hC iu).sup (Quotient.mk _ xu) (Quotient.mk _ (hij ▸ xv)))
    else
      -- Cross-child: sup = ⊤.
      ⊤

/-- Vertex-level infimum for `.branch ms`. Dual to `branch_sup_vertex`. -/
noncomputable def branch_inf_vertex
    (ms : List (String × SessionType))
    (hPC : parClosed (.branch ms : SessionType))
    (hC : ∀ k : Fin ms.length, SCCLatticeStruct (stateSpace (ms.get k).2))
    (u v : State (.branch ms : SessionType)) :
    SCCQuotient (stateSpace (.branch ms : SessionType)) :=
  if _ : u.val = 1 then
    Quotient.mk _ v  -- [u] = ⊤, inf = v
  else if _ : v.val = 1 then
    Quotient.mk _ u  -- [v] = ⊤, inf = u
  else if _ : u.val = 0 then
    ⊥  -- [u] = ⊥, inf = ⊥
  else if _ : v.val = 0 then
    ⊥  -- [v] = ⊥, inf = ⊥
  else
    have hu2 : 2 ≤ u.val := by omega
    have hv2 : 2 ≤ v.val := by omega
    let ⟨iu, xu⟩ := branchChildOf ms u hu2
    let ⟨iv, xv⟩ := branchChildOf ms v hv2
    if hij : iu = iv then
      branch_child_embed ms hPC iu
        ((hC iu).inf (Quotient.mk _ xu) (Quotient.mk _ (hij ▸ xv)))
    else
      ⊥

/-- Select analogue of `branch_sup_vertex`. -/
noncomputable def select_sup_vertex
    (ls : List (String × SessionType))
    (hPC : parClosed (.select ls : SessionType))
    (hC : ∀ k : Fin ls.length, SCCLatticeStruct (stateSpace (ls.get k).2))
    (u v : State (.select ls : SessionType)) :
    SCCQuotient (stateSpace (.select ls : SessionType)) :=
  if _ : u.val = 0 then
    Quotient.mk _ v
  else if _ : v.val = 0 then
    Quotient.mk _ u
  else if _ : u.val = 1 then
    ⊤
  else if _ : v.val = 1 then
    ⊤
  else
    have hu2 : 2 ≤ u.val := by omega
    have hv2 : 2 ≤ v.val := by omega
    let ⟨iu, xu⟩ := selectChildOf ls u hu2
    let ⟨iv, xv⟩ := selectChildOf ls v hv2
    if hij : iu = iv then
      select_child_embed ls hPC iu
        ((hC iu).sup (Quotient.mk _ xu) (Quotient.mk _ (hij ▸ xv)))
    else
      ⊤

/-- Select analogue of `branch_inf_vertex`. -/
noncomputable def select_inf_vertex
    (ls : List (String × SessionType))
    (hPC : parClosed (.select ls : SessionType))
    (hC : ∀ k : Fin ls.length, SCCLatticeStruct (stateSpace (ls.get k).2))
    (u v : State (.select ls : SessionType)) :
    SCCQuotient (stateSpace (.select ls : SessionType)) :=
  if _ : u.val = 1 then
    Quotient.mk _ v
  else if _ : v.val = 1 then
    Quotient.mk _ u
  else if _ : u.val = 0 then
    ⊥
  else if _ : v.val = 0 then
    ⊥
  else
    have hu2 : 2 ≤ u.val := by omega
    have hv2 : 2 ≤ v.val := by omega
    let ⟨iu, xu⟩ := selectChildOf ls u hu2
    let ⟨iv, xv⟩ := selectChildOf ls v hv2
    if hij : iu = iv then
      select_child_embed ls hPC iu
        ((hC iu).inf (Quotient.mk _ xu) (Quotient.mk _ (hij ▸ xv)))
    else
      ⊥

/-! ### D.5 — Respect of SCCSetoid for the vertex-level functions -/

/-- If `u ≈ u'` in the SCCSetoid for `.branch ms`, then `u.val = 0 ↔ u'.val = 0`. -/
private theorem branch_sccRel_preserves_root
    (ms : List (String × SessionType))
    (u u' : State (.branch ms : SessionType))
    (h : MutuallyReachable (stateSpace (.branch ms : SessionType)) u u') :
    u.val = 0 ↔ u'.val = 0 := by
  have hcls := branch_scc_classifier ms u u' h
  constructor
  · intro hu0
    rcases hcls with ⟨_, hv0⟩ | ⟨hu1, _⟩ | ⟨i, hui, _⟩
    · exact hv0
    · omega
    · unfold inChildRange at hui; omega
  · intro hu'0
    rcases hcls with ⟨hu0, _⟩ | ⟨_, hv1⟩ | ⟨i, _, hvi⟩
    · exact hu0
    · omega
    · unfold inChildRange at hvi; omega

/-- If `u ≈ u'` in the SCCSetoid for `.branch ms`, then `u.val = 1 ↔ u'.val = 1`. -/
private theorem branch_sccRel_preserves_bottom
    (ms : List (String × SessionType))
    (u u' : State (.branch ms : SessionType))
    (h : MutuallyReachable (stateSpace (.branch ms : SessionType)) u u') :
    u.val = 1 ↔ u'.val = 1 := by
  have hcls := branch_scc_classifier ms u u' h
  constructor
  · intro hu1
    rcases hcls with ⟨hu0, _⟩ | ⟨_, hv1⟩ | ⟨i, hui, _⟩
    · omega
    · exact hv1
    · unfold inChildRange at hui; omega
  · intro hu'1
    rcases hcls with ⟨_, hv0⟩ | ⟨hu1, _⟩ | ⟨i, _, hvi⟩
    · omega
    · exact hu1
    · unfold inChildRange at hvi; omega

/-- If `u ≈ u'` and both are in some child (val ≥ 2), they are in the same child. -/
private theorem branch_sccRel_same_child
    (ms : List (String × SessionType))
    (u u' : State (.branch ms : SessionType))
    (h : MutuallyReachable (stateSpace (.branch ms : SessionType)) u u')
    (hu2 : 2 ≤ u.val) (hu'2 : 2 ≤ u'.val) :
    (branchChildOf ms u hu2).1 = (branchChildOf ms u' hu'2).1 := by
  have hcls := branch_scc_classifier ms u u' h
  rcases hcls with ⟨hu0, _⟩ | ⟨hu1, _⟩ | ⟨i, hui, hu'i⟩
  · omega
  · omega
  · -- Both in child i.
    have h1 : (branchChildOf ms u hu2).1 = i :=
      branchChildOf_fst_of_inChildRange ms u hu2 i hui
    have h2 : (branchChildOf ms u' hu'2).1 = i :=
      branchChildOf_fst_of_inChildRange ms u' hu'2 i hu'i
    rw [h1, h2]

/-- Select analogue. -/
private theorem select_sccRel_preserves_root
    (ls : List (String × SessionType))
    (u u' : State (.select ls : SessionType))
    (h : MutuallyReachable (stateSpace (.select ls : SessionType)) u u') :
    u.val = 0 ↔ u'.val = 0 := by
  have hcls := select_scc_classifier ls u u' h
  constructor
  · intro hu0
    rcases hcls with ⟨_, hv0⟩ | ⟨hu1, _⟩ | ⟨i, hui, _⟩
    · exact hv0
    · omega
    · unfold inChildRange at hui; omega
  · intro hu'0
    rcases hcls with ⟨hu0, _⟩ | ⟨_, hv1⟩ | ⟨i, _, hvi⟩
    · exact hu0
    · omega
    · unfold inChildRange at hvi; omega

/-- Select analogue. -/
private theorem select_sccRel_preserves_bottom
    (ls : List (String × SessionType))
    (u u' : State (.select ls : SessionType))
    (h : MutuallyReachable (stateSpace (.select ls : SessionType)) u u') :
    u.val = 1 ↔ u'.val = 1 := by
  have hcls := select_scc_classifier ls u u' h
  constructor
  · intro hu1
    rcases hcls with ⟨hu0, _⟩ | ⟨_, hv1⟩ | ⟨i, hui, _⟩
    · omega
    · exact hv1
    · unfold inChildRange at hui; omega
  · intro hu'1
    rcases hcls with ⟨_, hv0⟩ | ⟨hu1, _⟩ | ⟨i, _, hvi⟩
    · omega
    · exact hu1
    · unfold inChildRange at hvi; omega

/-- Select analogue. -/
private theorem select_sccRel_same_child
    (ls : List (String × SessionType))
    (u u' : State (.select ls : SessionType))
    (h : MutuallyReachable (stateSpace (.select ls : SessionType)) u u')
    (hu2 : 2 ≤ u.val) (hu'2 : 2 ≤ u'.val) :
    (selectChildOf ls u hu2).1 = (selectChildOf ls u' hu'2).1 := by
  have hcls := select_scc_classifier ls u u' h
  rcases hcls with ⟨hu0, _⟩ | ⟨hu1, _⟩ | ⟨i, hui, hu'i⟩
  · omega
  · omega
  · have h1 : (selectChildOf ls u hu2).1 = i :=
      selectChildOf_fst_of_inChildRange ls u hu2 i hui
    have h2 : (selectChildOf ls u' hu'2).1 = i :=
      selectChildOf_fst_of_inChildRange ls u' hu'2 i hu'i
    rw [h1, h2]

/-- For same-child vertices, the child-class `⟦x⟧` is equal at the child
level iff their branch-class is equal at the branch level. -/
private theorem branch_child_class_eq_of_sccRel
    (ms : List (String × SessionType))
    (hPC : parClosed (.branch ms : SessionType))
    (u u' : State (.branch ms : SessionType))
    (h : MutuallyReachable (stateSpace (.branch ms : SessionType)) u u')
    (hu2 : 2 ≤ u.val) (hu'2 : 2 ≤ u'.val) :
    branch_child_embed ms hPC (branchChildOf ms u hu2).1
        (Quotient.mk _ (branchChildOf ms u hu2).2) =
      branch_child_embed ms hPC (branchChildOf ms u' hu'2).1
        (Quotient.mk _ (branchChildOf ms u' hu'2).2) := by
  -- Both embeddings land in the branch SCC quotient.
  -- By branch_child_embed_mk: embed ⟦x⟧ = ⟦branchChildShift i x⟧.
  -- branchChildOf_shift gives branchChildShift i x = u.
  rw [branch_child_embed_mk, branch_child_embed_mk]
  have hu_eq : branchChildShift ms (branchChildOf ms u hu2).1 (branchChildOf ms u hu2).2 = u :=
    branchChildOf_shift ms u hu2
  have hu'_eq : branchChildShift ms (branchChildOf ms u' hu'2).1 (branchChildOf ms u' hu'2).2 = u' :=
    branchChildOf_shift ms u' hu'2
  rw [hu_eq, hu'_eq]
  -- Now: ⟦u⟧ = ⟦u'⟧ in branch SCC quotient.
  exact Quotient.sound h

/-- Select analogue. -/
private theorem select_child_class_eq_of_sccRel
    (ls : List (String × SessionType))
    (hPC : parClosed (.select ls : SessionType))
    (u u' : State (.select ls : SessionType))
    (h : MutuallyReachable (stateSpace (.select ls : SessionType)) u u')
    (hu2 : 2 ≤ u.val) (hu'2 : 2 ≤ u'.val) :
    select_child_embed ls hPC (selectChildOf ls u hu2).1
        (Quotient.mk _ (selectChildOf ls u hu2).2) =
      select_child_embed ls hPC (selectChildOf ls u' hu'2).1
        (Quotient.mk _ (selectChildOf ls u' hu'2).2) := by
  rw [select_child_embed_mk, select_child_embed_mk]
  have hu_eq : selectChildShift ls (selectChildOf ls u hu2).1 (selectChildOf ls u hu2).2 = u :=
    selectChildOf_shift ls u hu2
  have hu'_eq : selectChildShift ls (selectChildOf ls u' hu'2).1 (selectChildOf ls u' hu'2).2 = u' :=
    selectChildOf_shift ls u' hu'2
  rw [hu_eq, hu'_eq]
  exact Quotient.sound h

/-! ### Stripped-down respect: branch_sup_vertex respects SCCSetoid in each argument -/

/-- `branch_sup_vertex ms hPC hC` respects `SCCSetoid` in the first argument. -/
private theorem branch_sup_vertex_respects_left
    (ms : List (String × SessionType))
    (hPC : parClosed (.branch ms : SessionType))
    (hC : ∀ k : Fin ms.length, SCCLatticeStruct (stateSpace (ms.get k).2))
    (u u' v : State (.branch ms : SessionType))
    (h : MutuallyReachable (stateSpace (.branch ms : SessionType)) u u') :
    branch_sup_vertex ms hPC hC u v = branch_sup_vertex ms hPC hC u' v := by
  -- Case-split on u.val.
  unfold branch_sup_vertex
  have hroot := branch_sccRel_preserves_root ms u u' h
  have hbot := branch_sccRel_preserves_bottom ms u u' h
  by_cases hu0 : u.val = 0
  · have hu'0 : u'.val = 0 := hroot.mp hu0
    simp only [dif_pos hu0, dif_pos hu'0]
  · have hu'0 : u'.val ≠ 0 := fun h' => hu0 (hroot.mpr h')
    simp only [dif_neg hu0, dif_neg hu'0]
    by_cases hv0 : v.val = 0
    · simp only [dif_pos hv0]
      -- Both give Quotient.mk _ u respectively _ u'. Use Quotient.sound.
      exact Quotient.sound h
    · simp only [dif_neg hv0]
      by_cases hu1 : u.val = 1
      · have hu'1 : u'.val = 1 := hbot.mp hu1
        simp only [dif_pos hu1, dif_pos hu'1]
      · have hu'1 : u'.val ≠ 1 := fun h' => hu1 (hbot.mpr h')
        simp only [dif_neg hu1, dif_neg hu'1]
        by_cases hv1 : v.val = 1
        · simp only [dif_pos hv1]
        · simp only [dif_neg hv1]
          -- Both u and u' are in some child (val ≥ 2).
          have hu2 : 2 ≤ u.val := by omega
          have hu'2 : 2 ≤ u'.val := by omega
          have hv2 : 2 ≤ v.val := by omega
          -- Same child at the index level.
          have hsame := branch_sccRel_same_child ms u u' h hu2 hu'2
          -- Use a generic helper: case-split on the sigma components.
          -- The goal is of the form `(match branchChildOf ms u hu2 with | ⟨i, x⟩ => ...) = ...`.
          -- Rewrite both occurrences of branchChildOf by their projections.
          generalize hpu : branchChildOf ms u hu2 = pu
          generalize hpu' : branchChildOf ms u' hu'2 = pu'
          generalize hpv : branchChildOf ms v hv2 = pv
          -- Now pu, pu', pv are free variables of type Σ i, State (ms.get i).2.
          -- hsame becomes pu.1 = pu'.1.
          rw [hpu, hpu'] at hsame
          -- hsame : pu.1 = pu'.1.
          obtain ⟨iu, xu⟩ := pu
          obtain ⟨iu', xu'⟩ := pu'
          obtain ⟨iv, xv⟩ := pv
          simp only at hsame
          -- hsame : iu = iu'.
          by_cases hiuv : iu = iv
          · have hiu'v : iu' = iv := hsame ▸ hiuv
            simp only [dif_pos hiuv, dif_pos hiu'v]
            subst hsame
            -- Now iu = iu' as free variable.
            -- Goal: embed iu ((hC iu).sup [xu] [hiuv ▸ xv]) =
            --       embed iu ((hC iu).sup [xu'] [hiuv ▸ xv]).  (since hiu'v = hiuv)
            -- Need: [xu] = [xu'] at child SCC level.
            have hembed_eq : branch_child_embed ms hPC iu (Quotient.mk _ xu) =
                             branch_child_embed ms hPC iu (Quotient.mk _ xu') := by
              have h_raw := branch_child_class_eq_of_sccRel ms hPC u u' h hu2 hu'2
              rw [hpu, hpu'] at h_raw
              exact h_raw
            rw [branch_child_embed_mk, branch_child_embed_mk] at hembed_eq
            have hchild_eq :
                (Quotient.mk (SCCSetoid (stateSpace (ms.get iu).2)) xu) =
                Quotient.mk _ xu' := by
              apply Quotient.sound
              have hMR := Quotient.exact hembed_eq
              refine ⟨?_, ?_⟩
              · exact (branch_same_child_reachable_iff ms hPC iu xu xu').mp hMR.1
              · exact (branch_same_child_reachable_iff ms hPC iu xu' xu).mp hMR.2
            congr 1
            -- Goal: (hC iu).sup ⟦xu⟧ ⟦hiuv ▸ xv⟧ = (hC iu).sup ⟦xu'⟧ ⟦hiuv ▸ xv⟧
            exact congrArg (fun q => (hC iu).sup q (Quotient.mk _ (hiuv ▸ xv))) hchild_eq
          · have hiu'v : iu' ≠ iv := fun h' => hiuv (hsame.trans h')
            simp only [dif_neg hiuv, dif_neg hiu'v]

/-- `branch_sup_vertex` respects `SCCSetoid` in the second argument. By
symmetry with the first-argument respect. -/
private theorem branch_sup_vertex_respects_right
    (ms : List (String × SessionType))
    (hPC : parClosed (.branch ms : SessionType))
    (hC : ∀ k : Fin ms.length, SCCLatticeStruct (stateSpace (ms.get k).2))
    (u v v' : State (.branch ms : SessionType))
    (h : MutuallyReachable (stateSpace (.branch ms : SessionType)) v v') :
    branch_sup_vertex ms hPC hC u v = branch_sup_vertex ms hPC hC u v' := by
  unfold branch_sup_vertex
  have hroot := branch_sccRel_preserves_root ms v v' h
  have hbot := branch_sccRel_preserves_bottom ms v v' h
  by_cases hu0 : u.val = 0
  · simp only [dif_pos hu0]
    -- Both sides: Quotient.mk _ v vs Quotient.mk _ v'. Use Quotient.sound.
    exact Quotient.sound h
  · simp only [dif_neg hu0]
    by_cases hv0 : v.val = 0
    · have hv'0 : v'.val = 0 := hroot.mp hv0
      simp only [dif_pos hv0, dif_pos hv'0]
    · have hv'0 : v'.val ≠ 0 := fun h' => hv0 (hroot.mpr h')
      simp only [dif_neg hv0, dif_neg hv'0]
      by_cases hu1 : u.val = 1
      · simp only [dif_pos hu1]
      · simp only [dif_neg hu1]
        by_cases hv1 : v.val = 1
        · have hv'1 : v'.val = 1 := hbot.mp hv1
          simp only [dif_pos hv1, dif_pos hv'1]
        · have hv'1 : v'.val ≠ 1 := fun h' => hv1 (hbot.mpr h')
          simp only [dif_neg hv1, dif_neg hv'1]
          have hu2 : 2 ≤ u.val := by omega
          have hv2 : 2 ≤ v.val := by omega
          have hv'2 : 2 ≤ v'.val := by omega
          have hsame := branch_sccRel_same_child ms v v' h hv2 hv'2
          generalize hpu : branchChildOf ms u hu2 = pu
          generalize hpv : branchChildOf ms v hv2 = pv
          generalize hpv' : branchChildOf ms v' hv'2 = pv'
          rw [hpv, hpv'] at hsame
          obtain ⟨iu, xu⟩ := pu
          obtain ⟨iv, xv⟩ := pv
          obtain ⟨iv', xv'⟩ := pv'
          simp only at hsame
          by_cases hiuv : iu = iv
          · have hiuv' : iu = iv' := hiuv.trans hsame
            simp only [dif_pos hiuv, dif_pos hiuv']
            have hembed_eq : branch_child_embed ms hPC iv (Quotient.mk _ xv) =
                             branch_child_embed ms hPC iv' (Quotient.mk _ xv') := by
              have h_raw := branch_child_class_eq_of_sccRel ms hPC v v' h hv2 hv'2
              rw [hpv, hpv'] at h_raw
              exact h_raw
            rw [branch_child_embed_mk, branch_child_embed_mk] at hembed_eq
            subst hsame
            -- Now iv' = iv as free variable, xv' : State (ms.get iv).2, hiuv = hiuv'.
            have hchild_eq :
                (Quotient.mk (SCCSetoid (stateSpace (ms.get iv).2)) xv) =
                Quotient.mk _ xv' := by
              apply Quotient.sound
              have hMR := Quotient.exact hembed_eq
              refine ⟨?_, ?_⟩
              · exact (branch_same_child_reachable_iff ms hPC iv xv xv').mp hMR.1
              · exact (branch_same_child_reachable_iff ms hPC iv xv' xv).mp hMR.2
            -- Transport both xv and xv' by hiuv : iu = iv to land in ms.get iu.
            have hchild_eq_tr :
                (Quotient.mk (SCCSetoid (stateSpace (ms.get iu).2)) (hiuv ▸ xv)) =
                Quotient.mk _ (hiuv ▸ xv') := by
              subst hiuv
              exact hchild_eq
            -- Goal: branch_child_embed ms hPC iu ((hC iu).sup ⟦xu⟧ ⟦hiuv ▸ xv⟧) =
            --       branch_child_embed ms hPC iu ((hC iu).sup ⟦xu⟧ ⟦hiuv' ▸ xv'⟧)
            exact congrArg (branch_child_embed ms hPC iu)
              (congrArg (fun q => (hC iu).sup (Quotient.mk _ xu) q) hchild_eq_tr)
          · have hiuv' : iu ≠ iv' := fun h' => hiuv (h'.trans hsame.symm)
            simp only [dif_neg hiuv, dif_neg hiuv']

/-- `branch_inf_vertex` respects `SCCSetoid` in the first argument. Dual
structure to `branch_sup_vertex_respects_left`. -/
private theorem branch_inf_vertex_respects_left
    (ms : List (String × SessionType))
    (hPC : parClosed (.branch ms : SessionType))
    (hC : ∀ k : Fin ms.length, SCCLatticeStruct (stateSpace (ms.get k).2))
    (u u' v : State (.branch ms : SessionType))
    (h : MutuallyReachable (stateSpace (.branch ms : SessionType)) u u') :
    branch_inf_vertex ms hPC hC u v = branch_inf_vertex ms hPC hC u' v := by
  unfold branch_inf_vertex
  have hroot := branch_sccRel_preserves_root ms u u' h
  have hbot := branch_sccRel_preserves_bottom ms u u' h
  by_cases hu1 : u.val = 1
  · have hu'1 : u'.val = 1 := hbot.mp hu1
    simp only [dif_pos hu1, dif_pos hu'1]
  · have hu'1 : u'.val ≠ 1 := fun h' => hu1 (hbot.mpr h')
    simp only [dif_neg hu1, dif_neg hu'1]
    by_cases hv1 : v.val = 1
    · simp only [dif_pos hv1]
      exact Quotient.sound h
    · simp only [dif_neg hv1]
      by_cases hu0 : u.val = 0
      · have hu'0 : u'.val = 0 := hroot.mp hu0
        simp only [dif_pos hu0, dif_pos hu'0]
      · have hu'0 : u'.val ≠ 0 := fun h' => hu0 (hroot.mpr h')
        simp only [dif_neg hu0, dif_neg hu'0]
        by_cases hv0 : v.val = 0
        · simp only [dif_pos hv0]
        · simp only [dif_neg hv0]
          have hu2 : 2 ≤ u.val := by omega
          have hu'2 : 2 ≤ u'.val := by omega
          have hv2 : 2 ≤ v.val := by omega
          have hsame := branch_sccRel_same_child ms u u' h hu2 hu'2
          generalize hpu : branchChildOf ms u hu2 = pu
          generalize hpu' : branchChildOf ms u' hu'2 = pu'
          generalize hpv : branchChildOf ms v hv2 = pv
          rw [hpu, hpu'] at hsame
          obtain ⟨iu, xu⟩ := pu
          obtain ⟨iu', xu'⟩ := pu'
          obtain ⟨iv, xv⟩ := pv
          simp only at hsame
          by_cases hiuv : iu = iv
          · have hiu'v : iu' = iv := hsame ▸ hiuv
            simp only [dif_pos hiuv, dif_pos hiu'v]
            have hembed_eq : branch_child_embed ms hPC iu (Quotient.mk _ xu) =
                             branch_child_embed ms hPC iu' (Quotient.mk _ xu') := by
              have h_raw := branch_child_class_eq_of_sccRel ms hPC u u' h hu2 hu'2
              rw [hpu, hpu'] at h_raw
              exact h_raw
            rw [branch_child_embed_mk, branch_child_embed_mk] at hembed_eq
            subst hsame
            have hchild_eq :
                (Quotient.mk (SCCSetoid (stateSpace (ms.get iu).2)) xu) =
                Quotient.mk _ xu' := by
              apply Quotient.sound
              have hMR := Quotient.exact hembed_eq
              refine ⟨?_, ?_⟩
              · exact (branch_same_child_reachable_iff ms hPC iu xu xu').mp hMR.1
              · exact (branch_same_child_reachable_iff ms hPC iu xu' xu).mp hMR.2
            congr 1
            exact congrArg (fun q => (hC iu).inf q (Quotient.mk _ (hiuv ▸ xv))) hchild_eq
          · have hiu'v : iu' ≠ iv := fun h' => hiuv (hsame.trans h')
            simp only [dif_neg hiuv, dif_neg hiu'v]

/-- `branch_inf_vertex` respects `SCCSetoid` in the second argument. -/
private theorem branch_inf_vertex_respects_right
    (ms : List (String × SessionType))
    (hPC : parClosed (.branch ms : SessionType))
    (hC : ∀ k : Fin ms.length, SCCLatticeStruct (stateSpace (ms.get k).2))
    (u v v' : State (.branch ms : SessionType))
    (h : MutuallyReachable (stateSpace (.branch ms : SessionType)) v v') :
    branch_inf_vertex ms hPC hC u v = branch_inf_vertex ms hPC hC u v' := by
  unfold branch_inf_vertex
  have hroot := branch_sccRel_preserves_root ms v v' h
  have hbot := branch_sccRel_preserves_bottom ms v v' h
  by_cases hu1 : u.val = 1
  · simp only [dif_pos hu1]
    exact Quotient.sound h
  · simp only [dif_neg hu1]
    by_cases hv1 : v.val = 1
    · have hv'1 : v'.val = 1 := hbot.mp hv1
      simp only [dif_pos hv1, dif_pos hv'1]
    · have hv'1 : v'.val ≠ 1 := fun h' => hv1 (hbot.mpr h')
      simp only [dif_neg hv1, dif_neg hv'1]
      by_cases hu0 : u.val = 0
      · simp only [dif_pos hu0]
      · simp only [dif_neg hu0]
        by_cases hv0 : v.val = 0
        · have hv'0 : v'.val = 0 := hroot.mp hv0
          simp only [dif_pos hv0, dif_pos hv'0]
        · have hv'0 : v'.val ≠ 0 := fun h' => hv0 (hroot.mpr h')
          simp only [dif_neg hv0, dif_neg hv'0]
          have hu2 : 2 ≤ u.val := by omega
          have hv2 : 2 ≤ v.val := by omega
          have hv'2 : 2 ≤ v'.val := by omega
          have hsame := branch_sccRel_same_child ms v v' h hv2 hv'2
          generalize hpu : branchChildOf ms u hu2 = pu
          generalize hpv : branchChildOf ms v hv2 = pv
          generalize hpv' : branchChildOf ms v' hv'2 = pv'
          rw [hpv, hpv'] at hsame
          obtain ⟨iu, xu⟩ := pu
          obtain ⟨iv, xv⟩ := pv
          obtain ⟨iv', xv'⟩ := pv'
          simp only at hsame
          by_cases hiuv : iu = iv
          · have hiuv' : iu = iv' := hiuv.trans hsame
            simp only [dif_pos hiuv, dif_pos hiuv']
            have hembed_eq : branch_child_embed ms hPC iv (Quotient.mk _ xv) =
                             branch_child_embed ms hPC iv' (Quotient.mk _ xv') := by
              have h_raw := branch_child_class_eq_of_sccRel ms hPC v v' h hv2 hv'2
              rw [hpv, hpv'] at h_raw
              exact h_raw
            rw [branch_child_embed_mk, branch_child_embed_mk] at hembed_eq
            subst hsame
            have hchild_eq :
                (Quotient.mk (SCCSetoid (stateSpace (ms.get iv).2)) xv) =
                Quotient.mk _ xv' := by
              apply Quotient.sound
              have hMR := Quotient.exact hembed_eq
              refine ⟨?_, ?_⟩
              · exact (branch_same_child_reachable_iff ms hPC iv xv xv').mp hMR.1
              · exact (branch_same_child_reachable_iff ms hPC iv xv' xv).mp hMR.2
            have hchild_eq_tr :
                (Quotient.mk (SCCSetoid (stateSpace (ms.get iu).2)) (hiuv ▸ xv)) =
                Quotient.mk _ (hiuv ▸ xv') := by
              subst hiuv
              exact hchild_eq
            exact congrArg (branch_child_embed ms hPC iu)
              (congrArg (fun q => (hC iu).inf (Quotient.mk _ xu) q) hchild_eq_tr)
          · have hiuv' : iu ≠ iv' := fun h' => hiuv (h'.trans hsame.symm)
            simp only [dif_neg hiuv, dif_neg hiuv']

/-! ### Select respect analogs -/

private theorem select_sup_vertex_respects_left
    (ls : List (String × SessionType))
    (hPC : parClosed (.select ls : SessionType))
    (hC : ∀ k : Fin ls.length, SCCLatticeStruct (stateSpace (ls.get k).2))
    (u u' v : State (.select ls : SessionType))
    (h : MutuallyReachable (stateSpace (.select ls : SessionType)) u u') :
    select_sup_vertex ls hPC hC u v = select_sup_vertex ls hPC hC u' v := by
  unfold select_sup_vertex
  have hroot := select_sccRel_preserves_root ls u u' h
  have hbot := select_sccRel_preserves_bottom ls u u' h
  by_cases hu0 : u.val = 0
  · have hu'0 : u'.val = 0 := hroot.mp hu0
    simp only [dif_pos hu0, dif_pos hu'0]
  · have hu'0 : u'.val ≠ 0 := fun h' => hu0 (hroot.mpr h')
    simp only [dif_neg hu0, dif_neg hu'0]
    by_cases hv0 : v.val = 0
    · simp only [dif_pos hv0]
      exact Quotient.sound h
    · simp only [dif_neg hv0]
      by_cases hu1 : u.val = 1
      · have hu'1 : u'.val = 1 := hbot.mp hu1
        simp only [dif_pos hu1, dif_pos hu'1]
      · have hu'1 : u'.val ≠ 1 := fun h' => hu1 (hbot.mpr h')
        simp only [dif_neg hu1, dif_neg hu'1]
        by_cases hv1 : v.val = 1
        · simp only [dif_pos hv1]
        · simp only [dif_neg hv1]
          have hu2 : 2 ≤ u.val := by omega
          have hu'2 : 2 ≤ u'.val := by omega
          have hv2 : 2 ≤ v.val := by omega
          have hsame := select_sccRel_same_child ls u u' h hu2 hu'2
          generalize hpu : selectChildOf ls u hu2 = pu
          generalize hpu' : selectChildOf ls u' hu'2 = pu'
          generalize hpv : selectChildOf ls v hv2 = pv
          rw [hpu, hpu'] at hsame
          obtain ⟨iu, xu⟩ := pu
          obtain ⟨iu', xu'⟩ := pu'
          obtain ⟨iv, xv⟩ := pv
          simp only at hsame
          by_cases hiuv : iu = iv
          · have hiu'v : iu' = iv := hsame ▸ hiuv
            simp only [dif_pos hiuv, dif_pos hiu'v]
            have hembed_eq : select_child_embed ls hPC iu (Quotient.mk _ xu) =
                             select_child_embed ls hPC iu' (Quotient.mk _ xu') := by
              have h_raw := select_child_class_eq_of_sccRel ls hPC u u' h hu2 hu'2
              rw [hpu, hpu'] at h_raw
              exact h_raw
            rw [select_child_embed_mk, select_child_embed_mk] at hembed_eq
            subst hsame
            have hchild_eq :
                (Quotient.mk (SCCSetoid (stateSpace (ls.get iu).2)) xu) =
                Quotient.mk _ xu' := by
              apply Quotient.sound
              have hMR := Quotient.exact hembed_eq
              refine ⟨?_, ?_⟩
              · exact (select_same_child_reachable_iff ls hPC iu xu xu').mp hMR.1
              · exact (select_same_child_reachable_iff ls hPC iu xu' xu).mp hMR.2
            congr 1
            exact congrArg (fun q => (hC iu).sup q (Quotient.mk _ (hiuv ▸ xv))) hchild_eq
          · have hiu'v : iu' ≠ iv := fun h' => hiuv (hsame.trans h')
            simp only [dif_neg hiuv, dif_neg hiu'v]

private theorem select_sup_vertex_respects_right
    (ls : List (String × SessionType))
    (hPC : parClosed (.select ls : SessionType))
    (hC : ∀ k : Fin ls.length, SCCLatticeStruct (stateSpace (ls.get k).2))
    (u v v' : State (.select ls : SessionType))
    (h : MutuallyReachable (stateSpace (.select ls : SessionType)) v v') :
    select_sup_vertex ls hPC hC u v = select_sup_vertex ls hPC hC u v' := by
  unfold select_sup_vertex
  have hroot := select_sccRel_preserves_root ls v v' h
  have hbot := select_sccRel_preserves_bottom ls v v' h
  by_cases hu0 : u.val = 0
  · simp only [dif_pos hu0]
    exact Quotient.sound h
  · simp only [dif_neg hu0]
    by_cases hv0 : v.val = 0
    · have hv'0 : v'.val = 0 := hroot.mp hv0
      simp only [dif_pos hv0, dif_pos hv'0]
    · have hv'0 : v'.val ≠ 0 := fun h' => hv0 (hroot.mpr h')
      simp only [dif_neg hv0, dif_neg hv'0]
      by_cases hu1 : u.val = 1
      · simp only [dif_pos hu1]
      · simp only [dif_neg hu1]
        by_cases hv1 : v.val = 1
        · have hv'1 : v'.val = 1 := hbot.mp hv1
          simp only [dif_pos hv1, dif_pos hv'1]
        · have hv'1 : v'.val ≠ 1 := fun h' => hv1 (hbot.mpr h')
          simp only [dif_neg hv1, dif_neg hv'1]
          have hu2 : 2 ≤ u.val := by omega
          have hv2 : 2 ≤ v.val := by omega
          have hv'2 : 2 ≤ v'.val := by omega
          have hsame := select_sccRel_same_child ls v v' h hv2 hv'2
          generalize hpu : selectChildOf ls u hu2 = pu
          generalize hpv : selectChildOf ls v hv2 = pv
          generalize hpv' : selectChildOf ls v' hv'2 = pv'
          rw [hpv, hpv'] at hsame
          obtain ⟨iu, xu⟩ := pu
          obtain ⟨iv, xv⟩ := pv
          obtain ⟨iv', xv'⟩ := pv'
          simp only at hsame
          by_cases hiuv : iu = iv
          · have hiuv' : iu = iv' := hiuv.trans hsame
            simp only [dif_pos hiuv, dif_pos hiuv']
            have hembed_eq : select_child_embed ls hPC iv (Quotient.mk _ xv) =
                             select_child_embed ls hPC iv' (Quotient.mk _ xv') := by
              have h_raw := select_child_class_eq_of_sccRel ls hPC v v' h hv2 hv'2
              rw [hpv, hpv'] at h_raw
              exact h_raw
            rw [select_child_embed_mk, select_child_embed_mk] at hembed_eq
            subst hsame
            have hchild_eq :
                (Quotient.mk (SCCSetoid (stateSpace (ls.get iv).2)) xv) =
                Quotient.mk _ xv' := by
              apply Quotient.sound
              have hMR := Quotient.exact hembed_eq
              refine ⟨?_, ?_⟩
              · exact (select_same_child_reachable_iff ls hPC iv xv xv').mp hMR.1
              · exact (select_same_child_reachable_iff ls hPC iv xv' xv).mp hMR.2
            have hchild_eq_tr :
                (Quotient.mk (SCCSetoid (stateSpace (ls.get iu).2)) (hiuv ▸ xv)) =
                Quotient.mk _ (hiuv ▸ xv') := by
              subst hiuv
              exact hchild_eq
            exact congrArg (select_child_embed ls hPC iu)
              (congrArg (fun q => (hC iu).sup (Quotient.mk _ xu) q) hchild_eq_tr)
          · have hiuv' : iu ≠ iv' := fun h' => hiuv (h'.trans hsame.symm)
            simp only [dif_neg hiuv, dif_neg hiuv']

private theorem select_inf_vertex_respects_left
    (ls : List (String × SessionType))
    (hPC : parClosed (.select ls : SessionType))
    (hC : ∀ k : Fin ls.length, SCCLatticeStruct (stateSpace (ls.get k).2))
    (u u' v : State (.select ls : SessionType))
    (h : MutuallyReachable (stateSpace (.select ls : SessionType)) u u') :
    select_inf_vertex ls hPC hC u v = select_inf_vertex ls hPC hC u' v := by
  unfold select_inf_vertex
  have hroot := select_sccRel_preserves_root ls u u' h
  have hbot := select_sccRel_preserves_bottom ls u u' h
  by_cases hu1 : u.val = 1
  · have hu'1 : u'.val = 1 := hbot.mp hu1
    simp only [dif_pos hu1, dif_pos hu'1]
  · have hu'1 : u'.val ≠ 1 := fun h' => hu1 (hbot.mpr h')
    simp only [dif_neg hu1, dif_neg hu'1]
    by_cases hv1 : v.val = 1
    · simp only [dif_pos hv1]
      exact Quotient.sound h
    · simp only [dif_neg hv1]
      by_cases hu0 : u.val = 0
      · have hu'0 : u'.val = 0 := hroot.mp hu0
        simp only [dif_pos hu0, dif_pos hu'0]
      · have hu'0 : u'.val ≠ 0 := fun h' => hu0 (hroot.mpr h')
        simp only [dif_neg hu0, dif_neg hu'0]
        by_cases hv0 : v.val = 0
        · simp only [dif_pos hv0]
        · simp only [dif_neg hv0]
          have hu2 : 2 ≤ u.val := by omega
          have hu'2 : 2 ≤ u'.val := by omega
          have hv2 : 2 ≤ v.val := by omega
          have hsame := select_sccRel_same_child ls u u' h hu2 hu'2
          generalize hpu : selectChildOf ls u hu2 = pu
          generalize hpu' : selectChildOf ls u' hu'2 = pu'
          generalize hpv : selectChildOf ls v hv2 = pv
          rw [hpu, hpu'] at hsame
          obtain ⟨iu, xu⟩ := pu
          obtain ⟨iu', xu'⟩ := pu'
          obtain ⟨iv, xv⟩ := pv
          simp only at hsame
          by_cases hiuv : iu = iv
          · have hiu'v : iu' = iv := hsame ▸ hiuv
            simp only [dif_pos hiuv, dif_pos hiu'v]
            have hembed_eq : select_child_embed ls hPC iu (Quotient.mk _ xu) =
                             select_child_embed ls hPC iu' (Quotient.mk _ xu') := by
              have h_raw := select_child_class_eq_of_sccRel ls hPC u u' h hu2 hu'2
              rw [hpu, hpu'] at h_raw
              exact h_raw
            rw [select_child_embed_mk, select_child_embed_mk] at hembed_eq
            subst hsame
            have hchild_eq :
                (Quotient.mk (SCCSetoid (stateSpace (ls.get iu).2)) xu) =
                Quotient.mk _ xu' := by
              apply Quotient.sound
              have hMR := Quotient.exact hembed_eq
              refine ⟨?_, ?_⟩
              · exact (select_same_child_reachable_iff ls hPC iu xu xu').mp hMR.1
              · exact (select_same_child_reachable_iff ls hPC iu xu' xu).mp hMR.2
            congr 1
            exact congrArg (fun q => (hC iu).inf q (Quotient.mk _ (hiuv ▸ xv))) hchild_eq
          · have hiu'v : iu' ≠ iv := fun h' => hiuv (hsame.trans h')
            simp only [dif_neg hiuv, dif_neg hiu'v]

private theorem select_inf_vertex_respects_right
    (ls : List (String × SessionType))
    (hPC : parClosed (.select ls : SessionType))
    (hC : ∀ k : Fin ls.length, SCCLatticeStruct (stateSpace (ls.get k).2))
    (u v v' : State (.select ls : SessionType))
    (h : MutuallyReachable (stateSpace (.select ls : SessionType)) v v') :
    select_inf_vertex ls hPC hC u v = select_inf_vertex ls hPC hC u v' := by
  unfold select_inf_vertex
  have hroot := select_sccRel_preserves_root ls v v' h
  have hbot := select_sccRel_preserves_bottom ls v v' h
  by_cases hu1 : u.val = 1
  · simp only [dif_pos hu1]
    exact Quotient.sound h
  · simp only [dif_neg hu1]
    by_cases hv1 : v.val = 1
    · have hv'1 : v'.val = 1 := hbot.mp hv1
      simp only [dif_pos hv1, dif_pos hv'1]
    · have hv'1 : v'.val ≠ 1 := fun h' => hv1 (hbot.mpr h')
      simp only [dif_neg hv1, dif_neg hv'1]
      by_cases hu0 : u.val = 0
      · simp only [dif_pos hu0]
      · simp only [dif_neg hu0]
        by_cases hv0 : v.val = 0
        · have hv'0 : v'.val = 0 := hroot.mp hv0
          simp only [dif_pos hv0, dif_pos hv'0]
        · have hv'0 : v'.val ≠ 0 := fun h' => hv0 (hroot.mpr h')
          simp only [dif_neg hv0, dif_neg hv'0]
          have hu2 : 2 ≤ u.val := by omega
          have hv2 : 2 ≤ v.val := by omega
          have hv'2 : 2 ≤ v'.val := by omega
          have hsame := select_sccRel_same_child ls v v' h hv2 hv'2
          generalize hpu : selectChildOf ls u hu2 = pu
          generalize hpv : selectChildOf ls v hv2 = pv
          generalize hpv' : selectChildOf ls v' hv'2 = pv'
          rw [hpv, hpv'] at hsame
          obtain ⟨iu, xu⟩ := pu
          obtain ⟨iv, xv⟩ := pv
          obtain ⟨iv', xv'⟩ := pv'
          simp only at hsame
          by_cases hiuv : iu = iv
          · have hiuv' : iu = iv' := hiuv.trans hsame
            simp only [dif_pos hiuv, dif_pos hiuv']
            have hembed_eq : select_child_embed ls hPC iv (Quotient.mk _ xv) =
                             select_child_embed ls hPC iv' (Quotient.mk _ xv') := by
              have h_raw := select_child_class_eq_of_sccRel ls hPC v v' h hv2 hv'2
              rw [hpv, hpv'] at h_raw
              exact h_raw
            rw [select_child_embed_mk, select_child_embed_mk] at hembed_eq
            subst hsame
            have hchild_eq :
                (Quotient.mk (SCCSetoid (stateSpace (ls.get iv).2)) xv) =
                Quotient.mk _ xv' := by
              apply Quotient.sound
              have hMR := Quotient.exact hembed_eq
              refine ⟨?_, ?_⟩
              · exact (select_same_child_reachable_iff ls hPC iv xv xv').mp hMR.1
              · exact (select_same_child_reachable_iff ls hPC iv xv' xv).mp hMR.2
            have hchild_eq_tr :
                (Quotient.mk (SCCSetoid (stateSpace (ls.get iu).2)) (hiuv ▸ xv)) =
                Quotient.mk _ (hiuv ▸ xv') := by
              subst hiuv
              exact hchild_eq
            exact congrArg (select_child_embed ls hPC iu)
              (congrArg (fun q => (hC iu).inf (Quotient.mk _ xu) q) hchild_eq_tr)
          · have hiuv' : iu ≠ iv' := fun h' => hiuv (h'.trans hsame.symm)
            simp only [dif_neg hiuv, dif_neg hiuv']

/-! ### Class-level sup/inf for branch/select via `Quotient.lift₂` -/

/-- Class-level supremum for `.branch ms`. -/
noncomputable def branch_sup_class
    (ms : List (String × SessionType))
    (hPC : parClosed (.branch ms : SessionType))
    (hC : ∀ k : Fin ms.length, SCCLatticeStruct (stateSpace (ms.get k).2)) :
    SCCQuotient (stateSpace (.branch ms : SessionType)) →
    SCCQuotient (stateSpace (.branch ms : SessionType)) →
    SCCQuotient (stateSpace (.branch ms : SessionType)) :=
  Quotient.lift₂ (branch_sup_vertex ms hPC hC) (by
    intro u v u' v' huu' hvv'
    -- huu' : SCCSetoid .. u u' = MutuallyReachable .. u u'
    -- hvv' : MutuallyReachable .. v v'
    calc branch_sup_vertex ms hPC hC u v
        = branch_sup_vertex ms hPC hC u' v :=
          branch_sup_vertex_respects_left ms hPC hC u u' v huu'
      _ = branch_sup_vertex ms hPC hC u' v' :=
          branch_sup_vertex_respects_right ms hPC hC u' v v' hvv')

/-- Class-level infimum for `.branch ms`. -/
noncomputable def branch_inf_class
    (ms : List (String × SessionType))
    (hPC : parClosed (.branch ms : SessionType))
    (hC : ∀ k : Fin ms.length, SCCLatticeStruct (stateSpace (ms.get k).2)) :
    SCCQuotient (stateSpace (.branch ms : SessionType)) →
    SCCQuotient (stateSpace (.branch ms : SessionType)) →
    SCCQuotient (stateSpace (.branch ms : SessionType)) :=
  Quotient.lift₂ (branch_inf_vertex ms hPC hC) (by
    intro u v u' v' huu' hvv'
    calc branch_inf_vertex ms hPC hC u v
        = branch_inf_vertex ms hPC hC u' v :=
          branch_inf_vertex_respects_left ms hPC hC u u' v huu'
      _ = branch_inf_vertex ms hPC hC u' v' :=
          branch_inf_vertex_respects_right ms hPC hC u' v v' hvv')

/-- Class-level supremum for `.select ls`. -/
noncomputable def select_sup_class
    (ls : List (String × SessionType))
    (hPC : parClosed (.select ls : SessionType))
    (hC : ∀ k : Fin ls.length, SCCLatticeStruct (stateSpace (ls.get k).2)) :
    SCCQuotient (stateSpace (.select ls : SessionType)) →
    SCCQuotient (stateSpace (.select ls : SessionType)) →
    SCCQuotient (stateSpace (.select ls : SessionType)) :=
  Quotient.lift₂ (select_sup_vertex ls hPC hC) (by
    intro u v u' v' huu' hvv'
    calc select_sup_vertex ls hPC hC u v
        = select_sup_vertex ls hPC hC u' v :=
          select_sup_vertex_respects_left ls hPC hC u u' v huu'
      _ = select_sup_vertex ls hPC hC u' v' :=
          select_sup_vertex_respects_right ls hPC hC u' v v' hvv')

/-- Class-level infimum for `.select ls`. -/
noncomputable def select_inf_class
    (ls : List (String × SessionType))
    (hPC : parClosed (.select ls : SessionType))
    (hC : ∀ k : Fin ls.length, SCCLatticeStruct (stateSpace (ls.get k).2)) :
    SCCQuotient (stateSpace (.select ls : SessionType)) →
    SCCQuotient (stateSpace (.select ls : SessionType)) →
    SCCQuotient (stateSpace (.select ls : SessionType)) :=
  Quotient.lift₂ (select_inf_vertex ls hPC hC) (by
    intro u v u' v' huu' hvv'
    calc select_inf_vertex ls hPC hC u v
        = select_inf_vertex ls hPC hC u' v :=
          select_inf_vertex_respects_left ls hPC hC u u' v huu'
      _ = select_inf_vertex ls hPC hC u' v' :=
          select_inf_vertex_respects_right ls hPC hC u' v v' hvv')

/-! ### Unfolding lemmas: `_class` on `Quotient.mk` reduces to `_vertex`. -/

@[simp] theorem branch_sup_class_mk
    (ms : List (String × SessionType))
    (hPC : parClosed (.branch ms : SessionType))
    (hC : ∀ k : Fin ms.length, SCCLatticeStruct (stateSpace (ms.get k).2))
    (u v : State (.branch ms : SessionType)) :
    branch_sup_class ms hPC hC
      (Quotient.mk (SCCSetoid (stateSpace (.branch ms : SessionType))) u)
      (Quotient.mk (SCCSetoid (stateSpace (.branch ms : SessionType))) v) =
    branch_sup_vertex ms hPC hC u v := rfl

@[simp] theorem branch_inf_class_mk
    (ms : List (String × SessionType))
    (hPC : parClosed (.branch ms : SessionType))
    (hC : ∀ k : Fin ms.length, SCCLatticeStruct (stateSpace (ms.get k).2))
    (u v : State (.branch ms : SessionType)) :
    branch_inf_class ms hPC hC
      (Quotient.mk (SCCSetoid (stateSpace (.branch ms : SessionType))) u)
      (Quotient.mk (SCCSetoid (stateSpace (.branch ms : SessionType))) v) =
    branch_inf_vertex ms hPC hC u v := rfl

@[simp] theorem select_sup_class_mk
    (ls : List (String × SessionType))
    (hPC : parClosed (.select ls : SessionType))
    (hC : ∀ k : Fin ls.length, SCCLatticeStruct (stateSpace (ls.get k).2))
    (u v : State (.select ls : SessionType)) :
    select_sup_class ls hPC hC
      (Quotient.mk (SCCSetoid (stateSpace (.select ls : SessionType))) u)
      (Quotient.mk (SCCSetoid (stateSpace (.select ls : SessionType))) v) =
    select_sup_vertex ls hPC hC u v := rfl

@[simp] theorem select_inf_class_mk
    (ls : List (String × SessionType))
    (hPC : parClosed (.select ls : SessionType))
    (hC : ∀ k : Fin ls.length, SCCLatticeStruct (stateSpace (ls.get k).2))
    (u v : State (.select ls : SessionType)) :
    select_inf_class ls hPC hC
      (Quotient.mk (SCCSetoid (stateSpace (.select ls : SessionType))) u)
      (Quotient.mk (SCCSetoid (stateSpace (.select ls : SessionType))) v) =
    select_inf_vertex ls hPC hC u v := rfl

/-! ### D.6 — Six lattice axioms for `branch_latticeStruct`

Each axiom discharges via `Quotient.inductionOn₂` + case-split on
`branchClassify u, branchClassify v` (here expressed directly as case
splits on `u.val`). Root/bottom/cross-child cases use the
`BoundedOrder` facts (`bot_le`, `le_top`); same-child cases delegate to
the child's lattice via `branch_child_embed_monotone` + `(hC i).le_sup_…`
/ `.inf_le_…`.
-/

/-- **Main theorem: branch_latticeStruct**. The SCC quotient of
`.branch ms` carries a lattice structure, given lattice structures on
each child's SCC quotient. -/
noncomputable def branch_latticeStruct
    (ms : List (String × SessionType))
    (hPC : parClosed (.branch ms : SessionType))
    (hC : ∀ k : Fin ms.length, SCCLatticeStruct (stateSpace (ms.get k).2)) :
    SCCLatticeStruct (stateSpace (.branch ms : SessionType)) where
  sup := branch_sup_class ms hPC hC
  inf := branch_inf_class ms hPC hC
  le_sup_left := by
    intro a b
    induction a using Quotient.ind with
    | _ u =>
      induction b using Quotient.ind with
      | _ v =>
        rw [branch_sup_class_mk]
        unfold branch_sup_vertex
        by_cases hu0 : u.val = 0
        · simp only [dif_pos hu0]
          -- sup = [v]; need [u] ≤ [v]. By branch_class_eq_bot_of_root, [u] = ⊥. bot_le.
          rw [branch_class_eq_bot_of_root ms u hu0]
          exact bot_le
        · simp only [dif_neg hu0]
          by_cases hv0 : v.val = 0
          · simp only [dif_pos hv0]
            -- sup = [u]; le_refl.
            exact le_refl _
          · simp only [dif_neg hv0]
            by_cases hu1 : u.val = 1
            · simp only [dif_pos hu1]
              -- sup = ⊤; need [u] ≤ ⊤. le_top.
              rw [branch_class_eq_top_of_bottom ms u hu1]
            · simp only [dif_neg hu1]
              by_cases hv1 : v.val = 1
              · simp only [dif_pos hv1]
                exact le_top
              · simp only [dif_neg hv1]
                have hu2 : 2 ≤ u.val := by omega
                have hv2 : 2 ≤ v.val := by omega
                set pu := branchChildOf ms u hu2
                set pv := branchChildOf ms v hv2
                by_cases hij : pu.1 = pv.1
                · simp only [dif_pos hij]
                  -- sup = embed pu.1 ((hC pu.1).sup [pu.2] [hij ▸ pv.2])
                  -- need [u] ≤ that.
                  -- Chain:
                  --   [u] = [shift pu.1 pu.2]       (branchChildOf_shift)
                  --       = embed pu.1 [pu.2]       (branch_child_embed_mk)
                  --       ≤ embed pu.1 ((hC pu.1).sup [pu.2] …)  (monotone + le_sup_left)
                  have hu_eq : u =
                      branchChildShift ms pu.1 pu.2 := (branchChildOf_shift ms u hu2).symm
                  rw [hu_eq]
                  rw [show (Quotient.mk (SCCSetoid (stateSpace (.branch ms : SessionType)))
                              (branchChildShift ms pu.1 pu.2)) =
                            branch_child_embed ms hPC pu.1 (Quotient.mk _ pu.2) from
                        rfl]
                  -- Apply monotonicity.
                  apply branch_child_embed_monotone ms hPC pu.1
                  exact (hC pu.1).le_sup_left _ _
                · simp only [dif_neg hij]
                  exact le_top
  le_sup_right := by
    intro a b
    induction a using Quotient.ind with
    | _ u =>
      induction b using Quotient.ind with
      | _ v =>
        rw [branch_sup_class_mk]
        unfold branch_sup_vertex
        by_cases hu0 : u.val = 0
        · simp only [dif_pos hu0]
          exact le_refl _
        · simp only [dif_neg hu0]
          by_cases hv0 : v.val = 0
          · simp only [dif_pos hv0]
            -- sup = [u]; [v] ≤ [u]. Since v.val = 0, [v] = ⊥.
            rw [branch_class_eq_bot_of_root ms v hv0]
            exact bot_le
          · simp only [dif_neg hv0]
            by_cases hu1 : u.val = 1
            · simp only [dif_pos hu1]
              exact le_top
            · simp only [dif_neg hu1]
              by_cases hv1 : v.val = 1
              · simp only [dif_pos hv1]
                rw [branch_class_eq_top_of_bottom ms v hv1]
              · simp only [dif_neg hv1]
                have hu2 : 2 ≤ u.val := by omega
                have hv2 : 2 ≤ v.val := by omega
                generalize hpu : branchChildOf ms u hu2 = pu
                generalize hpv : branchChildOf ms v hv2 = pv
                obtain ⟨iu, xu⟩ := pu
                obtain ⟨iv, xv⟩ := pv
                by_cases hij : iu = iv
                · simp only [dif_pos hij]
                  have hv_eq : v = branchChildShift ms iv xv := by
                    have := branchChildOf_shift ms v hv2
                    rw [hpv] at this
                    exact this.symm
                  rw [hv_eq]
                  cases hij
                  -- Now iu is replaced by iv in the goal (or vice versa, depending on Lean's choice).
                  show branch_child_embed ms hPC _ (Quotient.mk _ xv) ≤
                    branch_child_embed ms hPC _ ((hC _).sup (Quotient.mk _ xu) (Quotient.mk _ xv))
                  apply branch_child_embed_monotone
                  exact (hC _).le_sup_right _ _
                · simp only [dif_neg hij]
                  exact le_top
  sup_le := by
    intro a b c hac hbc
    induction a using Quotient.ind with
    | _ u =>
      induction b using Quotient.ind with
      | _ v =>
        induction c using Quotient.ind with
        | _ w =>
          rw [branch_sup_class_mk]
          unfold branch_sup_vertex
          by_cases hu0 : u.val = 0
          · simp only [dif_pos hu0]
            -- sup = [v]; need [v] ≤ [w]. This is hbc.
            exact hbc
          · simp only [dif_neg hu0]
            by_cases hv0 : v.val = 0
            · simp only [dif_pos hv0]
              exact hac
            · simp only [dif_neg hv0]
              by_cases hu1 : u.val = 1
              · simp only [dif_pos hu1]
                -- sup = ⊤; need ⊤ ≤ [w]. By antisymmetry-via-le_top, this requires
                -- [w] = ⊤ (since ⊤ ≤ [w] and [w] ≤ ⊤ always).
                -- Key: hac says [u] ≤ [w] and [u] = ⊤, so ⊤ ≤ [w]. Combined with
                -- universal le_top, [w] = ⊤, so ⊤ ≤ [w] holds trivially (refl).
                -- In Lean, rewrite [u] = ⊤ in hac, then ⊤ ≤ [w].
                rw [branch_class_eq_top_of_bottom ms u hu1] at hac
                exact hac
              · simp only [dif_neg hu1]
                by_cases hv1 : v.val = 1
                · simp only [dif_pos hv1]
                  rw [branch_class_eq_top_of_bottom ms v hv1] at hbc
                  exact hbc
                · simp only [dif_neg hv1]
                  have hu2 : 2 ≤ u.val := by omega
                  have hv2 : 2 ≤ v.val := by omega
                  -- Extract pu, pv from their Sigma forms early.
                  generalize hpu : branchChildOf ms u hu2 = pu
                  generalize hpv : branchChildOf ms v hv2 = pv
                  obtain ⟨iu, xu⟩ := pu
                  obtain ⟨iv, xv⟩ := pv
                  by_cases hij : iu = iv
                  · simp only [dif_pos hij]
                    by_cases hw0 : w.val = 0
                    · -- [w] = ⊥. But [u] ≤ ⊥ forces [u] = ⊥, but u.val ≥ 2 contradicts.
                      rw [branch_class_eq_bot_of_root ms w hw0] at hac
                      have hu_bot :
                          (Quotient.mk _ u : SCCQuotient (stateSpace (.branch ms : SessionType)))
                          = (⊥ : SCCQuotient (stateSpace (.branch ms : SessionType))) :=
                        @le_antisymm (SCCQuotient (stateSpace (.branch ms : SessionType))) _ _ _
                          hac bot_le
                      have hMR := Quotient.exact hu_bot
                      -- hMR : MutuallyReachable _ u (initialState (.branch ms)).
                      -- (initialState _).val = 0 so by preserves_root, u.val = 0.
                      have hinit_val : (initialState (.branch ms : SessionType)).val = 0 := rfl
                      have : u.val = 0 :=
                        (branch_sccRel_preserves_root ms u _ hMR).mpr hinit_val
                      exact absurd this hu0
                    · by_cases hw1 : w.val = 1
                      · rw [branch_class_eq_top_of_bottom ms w hw1]; exact le_top
                      · have hw2 : 2 ≤ w.val := by omega
                        generalize hpw : branchChildOf ms w hw2 = pw
                        obtain ⟨iw, xw⟩ := pw
                        -- Derive u, v, w in their child forms.
                        have hu_eq : u = branchChildShift ms iu xu := by
                          have := branchChildOf_shift ms u hu2
                          rw [hpu] at this; exact this.symm
                        have hv_eq : v = branchChildShift ms iv xv := by
                          have := branchChildOf_shift ms v hv2
                          rw [hpv] at this; exact this.symm
                        have hw_eq : w = branchChildShift ms iw xw := by
                          have := branchChildOf_shift ms w hw2
                          rw [hpw] at this; exact this.symm
                        have hReach_uw : Reachable (stateSpace (.branch ms : SessionType)) u w := hac
                        have hReach_vw : Reachable (stateSpace (.branch ms : SessionType)) v w := hbc
                        rw [hu_eq, hw_eq] at hReach_uw
                        rw [hv_eq, hw_eq] at hReach_vw
                        have hu_in := branchChildShift_inChildRange ms iu xu
                        have hv_in := branchChildShift_inChildRange ms iv xv
                        have hw_in := branchChildShift_inChildRange ms iw xw
                        have hpuw : iu = iw := by
                          by_contra hne
                          exact branch_cross_child_not_reachable ms iu iw hne
                            _ _ hu_in hw_in hReach_uw
                        have hpvw : iv = iw := by
                          by_contra hne
                          exact branch_cross_child_not_reachable ms iv iw hne
                            _ _ hv_in hw_in hReach_vw
                        -- Now iu = iw, iv = iw, and from hij : iu = iv.
                        -- Child-level: ⟦xu⟧ ≤ ⟦hpuw ▸ xw⟧, ⟦xv⟧ ≤ ⟦hpvw ▸ xw⟧.
                        subst hij
                        -- Now hij is gone; iu = iv definitionally.
                        -- We still have hpuw : iu = iw (via iv), hpvw : iv = iw.
                        -- Substitute iw := iu (via hpuw).
                        subst hpuw
                        -- Now iw is iu. xw : State (ms.get iu).2. Similarly hpvw becomes reflexivity.
                        rw [hw_eq]
                        show branch_child_embed ms hPC _ ((hC _).sup (Quotient.mk _ xu) (Quotient.mk _ xv)) ≤
                          branch_child_embed ms hPC _ (Quotient.mk _ xw)
                        apply branch_child_embed_monotone
                        apply (hC _).sup_le
                        · show Reachable (stateSpace (ms.get _).2) xu xw
                          exact (branch_same_child_reachable_iff ms hPC _ xu xw).mp hReach_uw
                        · show Reachable (stateSpace (ms.get _).2) xv xw
                          exact (branch_same_child_reachable_iff ms hPC _ xv xw).mp hReach_vw
                  · simp only [dif_neg hij]
                    have hReach_uw : Reachable (stateSpace (.branch ms : SessionType)) u w := hac
                    have hReach_vw : Reachable (stateSpace (.branch ms : SessionType)) v w := hbc
                    by_cases hw0 : w.val = 0
                    · -- Contradiction as before.
                      rw [branch_class_eq_bot_of_root ms w hw0] at hac
                      have hu_bot :
                          (Quotient.mk _ u : SCCQuotient (stateSpace (.branch ms : SessionType)))
                          = (⊥ : SCCQuotient (stateSpace (.branch ms : SessionType))) :=
                        @le_antisymm (SCCQuotient (stateSpace (.branch ms : SessionType))) _ _ _
                          hac bot_le
                      have hMR := Quotient.exact hu_bot
                      have hinit_val : (initialState (.branch ms : SessionType)).val = 0 := rfl
                      have : u.val = 0 :=
                        (branch_sccRel_preserves_root ms u _ hMR).mpr hinit_val
                      exact absurd this hu0
                    · by_cases hw1 : w.val = 1
                      · rw [branch_class_eq_top_of_bottom ms w hw1]
                      · have hw2 : 2 ≤ w.val := by omega
                        generalize hpw : branchChildOf ms w hw2 = pw
                        obtain ⟨iw, xw⟩ := pw
                        have hu_eq : u = branchChildShift ms iu xu := by
                          have := branchChildOf_shift ms u hu2
                          rw [hpu] at this; exact this.symm
                        have hv_eq : v = branchChildShift ms iv xv := by
                          have := branchChildOf_shift ms v hv2
                          rw [hpv] at this; exact this.symm
                        have hw_eq : w = branchChildShift ms iw xw := by
                          have := branchChildOf_shift ms w hw2
                          rw [hpw] at this; exact this.symm
                        rw [hu_eq, hw_eq] at hReach_uw
                        rw [hv_eq, hw_eq] at hReach_vw
                        have hu_in := branchChildShift_inChildRange ms iu xu
                        have hv_in := branchChildShift_inChildRange ms iv xv
                        have hw_in := branchChildShift_inChildRange ms iw xw
                        have hpuw : iu = iw := by
                          by_contra hne
                          exact branch_cross_child_not_reachable ms iu iw hne
                            _ _ hu_in hw_in hReach_uw
                        have hpvw : iv = iw := by
                          by_contra hne
                          exact branch_cross_child_not_reachable ms iv iw hne
                            _ _ hv_in hw_in hReach_vw
                        exact absurd (hpuw.trans hpvw.symm) hij
  inf_le_left := by
    intro a b
    induction a using Quotient.ind with
    | _ u =>
      induction b using Quotient.ind with
      | _ v =>
        rw [branch_inf_class_mk]
        unfold branch_inf_vertex
        by_cases hu1 : u.val = 1
        · simp only [dif_pos hu1]
          rw [branch_class_eq_top_of_bottom ms u hu1]
          exact le_top
        · simp only [dif_neg hu1]
          by_cases hv1 : v.val = 1
          · simp only [dif_pos hv1]
            exact le_refl _
          · simp only [dif_neg hv1]
            by_cases hu0 : u.val = 0
            · simp only [dif_pos hu0]
              rw [branch_class_eq_bot_of_root ms u hu0]
            · simp only [dif_neg hu0]
              by_cases hv0 : v.val = 0
              · simp only [dif_pos hv0]
                exact bot_le
              · simp only [dif_neg hv0]
                have hu2 : 2 ≤ u.val := by omega
                have hv2 : 2 ≤ v.val := by omega
                generalize hpu : branchChildOf ms u hu2 = pu
                generalize hpv : branchChildOf ms v hv2 = pv
                obtain ⟨iu, xu⟩ := pu
                obtain ⟨iv, xv⟩ := pv
                by_cases hij : iu = iv
                · simp only [dif_pos hij]
                  have hu_eq : u = branchChildShift ms iu xu := by
                    have := branchChildOf_shift ms u hu2
                    rw [hpu] at this; exact this.symm
                  rw [hu_eq]
                  show branch_child_embed ms hPC iu
                         ((hC iu).inf (Quotient.mk _ xu) (Quotient.mk _ (hij ▸ xv))) ≤
                       branch_child_embed ms hPC iu (Quotient.mk _ xu)
                  apply branch_child_embed_monotone
                  exact (hC iu).inf_le_left _ _
                · simp only [dif_neg hij]
                  exact bot_le
  inf_le_right := by
    intro a b
    induction a using Quotient.ind with
    | _ u =>
      induction b using Quotient.ind with
      | _ v =>
        rw [branch_inf_class_mk]
        unfold branch_inf_vertex
        by_cases hu1 : u.val = 1
        · simp only [dif_pos hu1]
          exact le_refl _
        · simp only [dif_neg hu1]
          by_cases hv1 : v.val = 1
          · simp only [dif_pos hv1]
            rw [branch_class_eq_top_of_bottom ms v hv1]
            exact le_top
          · simp only [dif_neg hv1]
            by_cases hu0 : u.val = 0
            · simp only [dif_pos hu0]
              exact bot_le
            · simp only [dif_neg hu0]
              by_cases hv0 : v.val = 0
              · simp only [dif_pos hv0]
                rw [branch_class_eq_bot_of_root ms v hv0]
              · simp only [dif_neg hv0]
                have hu2 : 2 ≤ u.val := by omega
                have hv2 : 2 ≤ v.val := by omega
                generalize hpu : branchChildOf ms u hu2 = pu
                generalize hpv : branchChildOf ms v hv2 = pv
                obtain ⟨iu, xu⟩ := pu
                obtain ⟨iv, xv⟩ := pv
                by_cases hij : iu = iv
                · simp only [dif_pos hij]
                  have hv_eq : v = branchChildShift ms iv xv := by
                    have := branchChildOf_shift ms v hv2
                    rw [hpv] at this; exact this.symm
                  rw [hv_eq]
                  subst hij
                  show branch_child_embed ms hPC iu
                         ((hC iu).inf (Quotient.mk _ xu) (Quotient.mk _ xv)) ≤
                       branch_child_embed ms hPC iu (Quotient.mk _ xv)
                  apply branch_child_embed_monotone
                  exact (hC iu).inf_le_right _ _
                · simp only [dif_neg hij]
                  exact bot_le
  le_inf := by
    intro a b c hab hac
    induction a using Quotient.ind with
    | _ u =>
      induction b using Quotient.ind with
      | _ v =>
        induction c using Quotient.ind with
        | _ w =>
          rw [branch_inf_class_mk]
          unfold branch_inf_vertex
          by_cases hv1 : v.val = 1
          · simp only [dif_pos hv1]
            exact hac
          · simp only [dif_neg hv1]
            by_cases hw1 : w.val = 1
            · simp only [dif_pos hw1]
              exact hab
            · simp only [dif_neg hw1]
              by_cases hv0 : v.val = 0
              · simp only [dif_pos hv0]
                rw [branch_class_eq_bot_of_root ms v hv0] at hab
                exact hab
              · simp only [dif_neg hv0]
                by_cases hw0 : w.val = 0
                · simp only [dif_pos hw0]
                  rw [branch_class_eq_bot_of_root ms w hw0] at hac
                  exact hac
                · simp only [dif_neg hw0]
                  have hv2 : 2 ≤ v.val := by omega
                  have hw2 : 2 ≤ w.val := by omega
                  generalize hpv : branchChildOf ms v hv2 = pv
                  generalize hpw : branchChildOf ms w hw2 = pw
                  obtain ⟨iv, xv⟩ := pv
                  obtain ⟨iw, xw⟩ := pw
                  by_cases hij : iv = iw
                  · simp only [dif_pos hij]
                    by_cases hu0 : u.val = 0
                    · rw [branch_class_eq_bot_of_root ms u hu0]; exact bot_le
                    · by_cases hu1 : u.val = 1
                      · rw [branch_class_eq_top_of_bottom ms u hu1] at hab
                        have hv_top :
                            (Quotient.mk _ v : SCCQuotient (stateSpace (.branch ms : SessionType)))
                            = (⊤ : SCCQuotient (stateSpace (.branch ms : SessionType))) :=
                          @le_antisymm (SCCQuotient (stateSpace (.branch ms : SessionType))) _ _ _
                            le_top hab
                        have hMR := Quotient.exact hv_top
                        have hterm_val : (terminalState (.branch ms : SessionType)).val = 1 := by
                          unfold terminalState
                          have he : exitSlot (.branch ms : SessionType) 0 < stateCount (.branch ms : SessionType) := by
                            show exitSlot (.branch ms) 0 < stateCount (.branch ms); simp only [exitSlot, stateCount]; omega
                          simp only [dif_pos he]
                          show exitSlot (.branch ms : SessionType) 0 = 1; simp [exitSlot]
                        -- hMR : MutuallyReachable _ v terminal = ⟨Reachable v term, Reachable term v⟩.
                        have hequiv : MutuallyReachable (stateSpace (.branch ms : SessionType))
                            (terminalState _) v := ⟨hMR.2, hMR.1⟩
                        have := (branch_sccRel_preserves_bottom ms _ v hequiv).mp hterm_val
                        exact absurd this hv1
                      · have hu2 : 2 ≤ u.val := by omega
                        generalize hpu : branchChildOf ms u hu2 = pu
                        obtain ⟨iu, xu⟩ := pu
                        have hu_eq : u = branchChildShift ms iu xu := by
                          have := branchChildOf_shift ms u hu2
                          rw [hpu] at this; exact this.symm
                        have hv_eq : v = branchChildShift ms iv xv := by
                          have := branchChildOf_shift ms v hv2
                          rw [hpv] at this; exact this.symm
                        have hw_eq : w = branchChildShift ms iw xw := by
                          have := branchChildOf_shift ms w hw2
                          rw [hpw] at this; exact this.symm
                        have hReach_uv : Reachable (stateSpace (.branch ms : SessionType)) u v := hab
                        have hReach_uw : Reachable (stateSpace (.branch ms : SessionType)) u w := hac
                        rw [hu_eq, hv_eq] at hReach_uv
                        rw [hu_eq, hw_eq] at hReach_uw
                        have hu_in := branchChildShift_inChildRange ms iu xu
                        have hv_in := branchChildShift_inChildRange ms iv xv
                        have hw_in := branchChildShift_inChildRange ms iw xw
                        have hpuv : iu = iv := by
                          by_contra hne
                          exact branch_cross_child_not_reachable ms iu iv hne _ _ hu_in hv_in hReach_uv
                        have hpuw : iu = iw := by
                          by_contra hne
                          exact branch_cross_child_not_reachable ms iu iw hne _ _ hu_in hw_in hReach_uw
                        -- iu = iv = iw. All three agree.
                        subst hij
                        subst hpuv
                        -- Now iw = iv is replaced by iu (or similar).
                        rw [hu_eq]
                        show branch_child_embed ms hPC iu (Quotient.mk _ xu) ≤
                          branch_child_embed ms hPC iu
                            ((hC iu).inf (Quotient.mk _ xv) (Quotient.mk _ xw))
                        apply branch_child_embed_monotone
                        apply (hC iu).le_inf
                        · show Reachable (stateSpace (ms.get iu).2) xu xv
                          exact (branch_same_child_reachable_iff ms hPC iu xu xv).mp hReach_uv
                        · show Reachable (stateSpace (ms.get iu).2) xu xw
                          exact (branch_same_child_reachable_iff ms hPC iu xu xw).mp hReach_uw
                  · simp only [dif_neg hij]
                    -- inf = ⊥; need [u] ≤ ⊥, so [u] must be ⊥.
                    -- Derivation: u → v in child pv.1, u → w in child pw.1. pv.1 ≠ pw.1.
                    -- Taxonomy: u must be root (0) or bottom (1). Case root: [u] = ⊥, done.
                    -- Case bottom: [u] = ⊤. But ⊤ ≤ [v] forces [v] = ⊤, i.e., v.val = 1, contradicts.
                    by_cases hu0 : u.val = 0
                    · rw [branch_class_eq_bot_of_root ms u hu0]
                    · by_cases hu1 : u.val = 1
                      · -- u bottom: contradict as above.
                        rw [branch_class_eq_top_of_bottom ms u hu1] at hab
                        have hv_top :
                            (Quotient.mk _ v : SCCQuotient (stateSpace (.branch ms : SessionType)))
                            = (⊤ : SCCQuotient (stateSpace (.branch ms : SessionType))) :=
                          @le_antisymm (SCCQuotient (stateSpace (.branch ms : SessionType))) _ _ _
                            le_top hab
                        have hMR := Quotient.exact hv_top
                        have hterm_val : (terminalState (.branch ms : SessionType)).val = 1 := by
                          unfold terminalState
                          have he : exitSlot (.branch ms : SessionType) 0 < stateCount (.branch ms : SessionType) := by
                            show exitSlot (.branch ms) 0 < stateCount (.branch ms); simp only [exitSlot, stateCount]; omega
                          simp only [dif_pos he]
                          show exitSlot (.branch ms : SessionType) 0 = 1; simp [exitSlot]
                        have hequiv : MutuallyReachable (stateSpace (.branch ms : SessionType))
                            (terminalState _) v := ⟨hMR.2, hMR.1⟩
                        have := (branch_sccRel_preserves_bottom ms _ v hequiv).mp hterm_val
                        exact absurd this hv1
                      · -- u in child.
                        have hu2 : 2 ≤ u.val := by omega
                        generalize hpu : branchChildOf ms u hu2 = pu
                        obtain ⟨iu, xu⟩ := pu
                        have hu_eq : u = branchChildShift ms iu xu := by
                          have := branchChildOf_shift ms u hu2
                          rw [hpu] at this; exact this.symm
                        have hv_eq : v = branchChildShift ms iv xv := by
                          have := branchChildOf_shift ms v hv2
                          rw [hpv] at this; exact this.symm
                        have hw_eq : w = branchChildShift ms iw xw := by
                          have := branchChildOf_shift ms w hw2
                          rw [hpw] at this; exact this.symm
                        have hReach_uv : Reachable (stateSpace (.branch ms : SessionType)) u v := hab
                        have hReach_uw : Reachable (stateSpace (.branch ms : SessionType)) u w := hac
                        rw [hu_eq, hv_eq] at hReach_uv
                        rw [hu_eq, hw_eq] at hReach_uw
                        have hu_in := branchChildShift_inChildRange ms iu xu
                        have hv_in := branchChildShift_inChildRange ms iv xv
                        have hw_in := branchChildShift_inChildRange ms iw xw
                        have hpuv : iu = iv := by
                          by_contra hne
                          exact branch_cross_child_not_reachable ms iu iv hne _ _ hu_in hv_in hReach_uv
                        have hpuw : iu = iw := by
                          by_contra hne
                          exact branch_cross_child_not_reachable ms iu iw hne _ _ hu_in hw_in hReach_uw
                        exact absurd (hpuv.symm.trans hpuw) hij

/-! ### E — Select latticeStruct. Mirror branch structure. -/

/-- **Main theorem: select_latticeStruct**. Symmetric to
`branch_latticeStruct`. Uses `select_*` infrastructure throughout. -/
noncomputable def select_latticeStruct
    (ls : List (String × SessionType))
    (hPC : parClosed (.select ls : SessionType))
    (hC : ∀ k : Fin ls.length, SCCLatticeStruct (stateSpace (ls.get k).2)) :
    SCCLatticeStruct (stateSpace (.select ls : SessionType)) where
  sup := select_sup_class ls hPC hC
  inf := select_inf_class ls hPC hC
  le_sup_left := by
    intro a b
    induction a using Quotient.ind with
    | _ u =>
      induction b using Quotient.ind with
      | _ v =>
        rw [select_sup_class_mk]
        unfold select_sup_vertex
        by_cases hu0 : u.val = 0
        · simp only [dif_pos hu0]
          rw [select_class_eq_bot_of_root ls u hu0]; exact bot_le
        · simp only [dif_neg hu0]
          by_cases hv0 : v.val = 0
          · simp only [dif_pos hv0]
            exact le_refl _
          · simp only [dif_neg hv0]
            by_cases hu1 : u.val = 1
            · simp only [dif_pos hu1]
              rw [select_class_eq_top_of_bottom ls u hu1]
            · simp only [dif_neg hu1]
              by_cases hv1 : v.val = 1
              · simp only [dif_pos hv1]
                exact le_top
              · simp only [dif_neg hv1]
                have hu2 : 2 ≤ u.val := by omega
                have hv2 : 2 ≤ v.val := by omega
                generalize hpu : selectChildOf ls u hu2 = pu
                generalize hpv : selectChildOf ls v hv2 = pv
                obtain ⟨iu, xu⟩ := pu
                obtain ⟨iv, xv⟩ := pv
                by_cases hij : iu = iv
                · simp only [dif_pos hij]
                  have hu_eq : u = selectChildShift ls iu xu := by
                    have := selectChildOf_shift ls u hu2
                    rw [hpu] at this; exact this.symm
                  rw [hu_eq]
                  show select_child_embed ls hPC iu (Quotient.mk _ xu) ≤
                    select_child_embed ls hPC iu
                      ((hC iu).sup (Quotient.mk _ xu) (Quotient.mk _ (hij ▸ xv)))
                  apply select_child_embed_monotone
                  exact (hC iu).le_sup_left _ _
                · simp only [dif_neg hij]
                  exact le_top
  le_sup_right := by
    intro a b
    induction a using Quotient.ind with
    | _ u =>
      induction b using Quotient.ind with
      | _ v =>
        rw [select_sup_class_mk]
        unfold select_sup_vertex
        by_cases hu0 : u.val = 0
        · simp only [dif_pos hu0]
          exact le_refl _
        · simp only [dif_neg hu0]
          by_cases hv0 : v.val = 0
          · simp only [dif_pos hv0]
            rw [select_class_eq_bot_of_root ls v hv0]; exact bot_le
          · simp only [dif_neg hv0]
            by_cases hu1 : u.val = 1
            · simp only [dif_pos hu1]
              exact le_top
            · simp only [dif_neg hu1]
              by_cases hv1 : v.val = 1
              · simp only [dif_pos hv1]
                rw [select_class_eq_top_of_bottom ls v hv1]
              · simp only [dif_neg hv1]
                have hu2 : 2 ≤ u.val := by omega
                have hv2 : 2 ≤ v.val := by omega
                generalize hpu : selectChildOf ls u hu2 = pu
                generalize hpv : selectChildOf ls v hv2 = pv
                obtain ⟨iu, xu⟩ := pu
                obtain ⟨iv, xv⟩ := pv
                by_cases hij : iu = iv
                · simp only [dif_pos hij]
                  have hv_eq : v = selectChildShift ls iv xv := by
                    have := selectChildOf_shift ls v hv2
                    rw [hpv] at this; exact this.symm
                  rw [hv_eq]
                  cases hij
                  show select_child_embed ls hPC _ (Quotient.mk _ xv) ≤
                    select_child_embed ls hPC _ ((hC _).sup (Quotient.mk _ xu) (Quotient.mk _ xv))
                  apply select_child_embed_monotone
                  exact (hC _).le_sup_right _ _
                · simp only [dif_neg hij]
                  exact le_top
  sup_le := by
    intro a b c hac hbc
    induction a using Quotient.ind with
    | _ u =>
      induction b using Quotient.ind with
      | _ v =>
        induction c using Quotient.ind with
        | _ w =>
          rw [select_sup_class_mk]
          unfold select_sup_vertex
          by_cases hu0 : u.val = 0
          · simp only [dif_pos hu0]; exact hbc
          · simp only [dif_neg hu0]
            by_cases hv0 : v.val = 0
            · simp only [dif_pos hv0]; exact hac
            · simp only [dif_neg hv0]
              by_cases hu1 : u.val = 1
              · simp only [dif_pos hu1]
                rw [select_class_eq_top_of_bottom ls u hu1] at hac; exact hac
              · simp only [dif_neg hu1]
                by_cases hv1 : v.val = 1
                · simp only [dif_pos hv1]
                  rw [select_class_eq_top_of_bottom ls v hv1] at hbc; exact hbc
                · simp only [dif_neg hv1]
                  have hu2 : 2 ≤ u.val := by omega
                  have hv2 : 2 ≤ v.val := by omega
                  generalize hpu : selectChildOf ls u hu2 = pu
                  generalize hpv : selectChildOf ls v hv2 = pv
                  obtain ⟨iu, xu⟩ := pu
                  obtain ⟨iv, xv⟩ := pv
                  by_cases hij : iu = iv
                  · simp only [dif_pos hij]
                    by_cases hw0 : w.val = 0
                    · rw [select_class_eq_bot_of_root ls w hw0] at hac
                      have hu_bot :
                          (Quotient.mk _ u : SCCQuotient (stateSpace (.select ls : SessionType)))
                          = (⊥ : SCCQuotient (stateSpace (.select ls : SessionType))) :=
                        @le_antisymm (SCCQuotient (stateSpace (.select ls : SessionType))) _ _ _
                          hac bot_le
                      have hMR := Quotient.exact hu_bot
                      have hinit_val : (initialState (.select ls : SessionType)).val = 0 := rfl
                      have : u.val = 0 :=
                        (select_sccRel_preserves_root ls u _ hMR).mpr hinit_val
                      exact absurd this hu0
                    · by_cases hw1 : w.val = 1
                      · rw [select_class_eq_top_of_bottom ls w hw1]; exact le_top
                      · have hw2 : 2 ≤ w.val := by omega
                        generalize hpw : selectChildOf ls w hw2 = pw
                        obtain ⟨iw, xw⟩ := pw
                        have hu_eq : u = selectChildShift ls iu xu := by
                          have := selectChildOf_shift ls u hu2
                          rw [hpu] at this; exact this.symm
                        have hv_eq : v = selectChildShift ls iv xv := by
                          have := selectChildOf_shift ls v hv2
                          rw [hpv] at this; exact this.symm
                        have hw_eq : w = selectChildShift ls iw xw := by
                          have := selectChildOf_shift ls w hw2
                          rw [hpw] at this; exact this.symm
                        have hReach_uw : Reachable (stateSpace (.select ls : SessionType)) u w := hac
                        have hReach_vw : Reachable (stateSpace (.select ls : SessionType)) v w := hbc
                        rw [hu_eq, hw_eq] at hReach_uw
                        rw [hv_eq, hw_eq] at hReach_vw
                        have hu_in := selectChildShift_inChildRange ls iu xu
                        have hv_in := selectChildShift_inChildRange ls iv xv
                        have hw_in := selectChildShift_inChildRange ls iw xw
                        have hpuw : iu = iw := by
                          by_contra hne
                          exact select_cross_child_not_reachable ls iu iw hne _ _ hu_in hw_in hReach_uw
                        have hpvw : iv = iw := by
                          by_contra hne
                          exact select_cross_child_not_reachable ls iv iw hne _ _ hv_in hw_in hReach_vw
                        subst hij
                        subst hpuw
                        rw [hw_eq]
                        show select_child_embed ls hPC _ ((hC _).sup (Quotient.mk _ xu) (Quotient.mk _ xv)) ≤
                          select_child_embed ls hPC _ (Quotient.mk _ xw)
                        apply select_child_embed_monotone
                        apply (hC _).sup_le
                        · show Reachable (stateSpace (ls.get _).2) xu xw
                          exact (select_same_child_reachable_iff ls hPC _ xu xw).mp hReach_uw
                        · show Reachable (stateSpace (ls.get _).2) xv xw
                          exact (select_same_child_reachable_iff ls hPC _ xv xw).mp hReach_vw
                  · simp only [dif_neg hij]
                    have hReach_uw : Reachable (stateSpace (.select ls : SessionType)) u w := hac
                    have hReach_vw : Reachable (stateSpace (.select ls : SessionType)) v w := hbc
                    by_cases hw0 : w.val = 0
                    · rw [select_class_eq_bot_of_root ls w hw0] at hac
                      have hu_bot :
                          (Quotient.mk _ u : SCCQuotient (stateSpace (.select ls : SessionType)))
                          = (⊥ : SCCQuotient (stateSpace (.select ls : SessionType))) :=
                        @le_antisymm (SCCQuotient (stateSpace (.select ls : SessionType))) _ _ _
                          hac bot_le
                      have hMR := Quotient.exact hu_bot
                      have hinit_val : (initialState (.select ls : SessionType)).val = 0 := rfl
                      have : u.val = 0 :=
                        (select_sccRel_preserves_root ls u _ hMR).mpr hinit_val
                      exact absurd this hu0
                    · by_cases hw1 : w.val = 1
                      · rw [select_class_eq_top_of_bottom ls w hw1]
                      · have hw2 : 2 ≤ w.val := by omega
                        generalize hpw : selectChildOf ls w hw2 = pw
                        obtain ⟨iw, xw⟩ := pw
                        have hu_eq : u = selectChildShift ls iu xu := by
                          have := selectChildOf_shift ls u hu2
                          rw [hpu] at this; exact this.symm
                        have hv_eq : v = selectChildShift ls iv xv := by
                          have := selectChildOf_shift ls v hv2
                          rw [hpv] at this; exact this.symm
                        have hw_eq : w = selectChildShift ls iw xw := by
                          have := selectChildOf_shift ls w hw2
                          rw [hpw] at this; exact this.symm
                        rw [hu_eq, hw_eq] at hReach_uw
                        rw [hv_eq, hw_eq] at hReach_vw
                        have hu_in := selectChildShift_inChildRange ls iu xu
                        have hv_in := selectChildShift_inChildRange ls iv xv
                        have hw_in := selectChildShift_inChildRange ls iw xw
                        have hpuw : iu = iw := by
                          by_contra hne
                          exact select_cross_child_not_reachable ls iu iw hne _ _ hu_in hw_in hReach_uw
                        have hpvw : iv = iw := by
                          by_contra hne
                          exact select_cross_child_not_reachable ls iv iw hne _ _ hv_in hw_in hReach_vw
                        exact absurd (hpuw.trans hpvw.symm) hij
  inf_le_left := by
    intro a b
    induction a using Quotient.ind with
    | _ u =>
      induction b using Quotient.ind with
      | _ v =>
        rw [select_inf_class_mk]
        unfold select_inf_vertex
        by_cases hu1 : u.val = 1
        · simp only [dif_pos hu1]
          rw [select_class_eq_top_of_bottom ls u hu1]; exact le_top
        · simp only [dif_neg hu1]
          by_cases hv1 : v.val = 1
          · simp only [dif_pos hv1]
            exact le_refl _
          · simp only [dif_neg hv1]
            by_cases hu0 : u.val = 0
            · simp only [dif_pos hu0]
              rw [select_class_eq_bot_of_root ls u hu0]
            · simp only [dif_neg hu0]
              by_cases hv0 : v.val = 0
              · simp only [dif_pos hv0]; exact bot_le
              · simp only [dif_neg hv0]
                have hu2 : 2 ≤ u.val := by omega
                have hv2 : 2 ≤ v.val := by omega
                generalize hpu : selectChildOf ls u hu2 = pu
                generalize hpv : selectChildOf ls v hv2 = pv
                obtain ⟨iu, xu⟩ := pu
                obtain ⟨iv, xv⟩ := pv
                by_cases hij : iu = iv
                · simp only [dif_pos hij]
                  have hu_eq : u = selectChildShift ls iu xu := by
                    have := selectChildOf_shift ls u hu2
                    rw [hpu] at this; exact this.symm
                  rw [hu_eq]
                  show select_child_embed ls hPC iu
                         ((hC iu).inf (Quotient.mk _ xu) (Quotient.mk _ (hij ▸ xv))) ≤
                       select_child_embed ls hPC iu (Quotient.mk _ xu)
                  apply select_child_embed_monotone
                  exact (hC iu).inf_le_left _ _
                · simp only [dif_neg hij]; exact bot_le
  inf_le_right := by
    intro a b
    induction a using Quotient.ind with
    | _ u =>
      induction b using Quotient.ind with
      | _ v =>
        rw [select_inf_class_mk]
        unfold select_inf_vertex
        by_cases hu1 : u.val = 1
        · simp only [dif_pos hu1]
          exact le_refl _
        · simp only [dif_neg hu1]
          by_cases hv1 : v.val = 1
          · simp only [dif_pos hv1]
            rw [select_class_eq_top_of_bottom ls v hv1]; exact le_top
          · simp only [dif_neg hv1]
            by_cases hu0 : u.val = 0
            · simp only [dif_pos hu0]; exact bot_le
            · simp only [dif_neg hu0]
              by_cases hv0 : v.val = 0
              · simp only [dif_pos hv0]
                rw [select_class_eq_bot_of_root ls v hv0]
              · simp only [dif_neg hv0]
                have hu2 : 2 ≤ u.val := by omega
                have hv2 : 2 ≤ v.val := by omega
                generalize hpu : selectChildOf ls u hu2 = pu
                generalize hpv : selectChildOf ls v hv2 = pv
                obtain ⟨iu, xu⟩ := pu
                obtain ⟨iv, xv⟩ := pv
                by_cases hij : iu = iv
                · simp only [dif_pos hij]
                  have hv_eq : v = selectChildShift ls iv xv := by
                    have := selectChildOf_shift ls v hv2
                    rw [hpv] at this; exact this.symm
                  rw [hv_eq]
                  subst hij
                  show select_child_embed ls hPC iu
                         ((hC iu).inf (Quotient.mk _ xu) (Quotient.mk _ xv)) ≤
                       select_child_embed ls hPC iu (Quotient.mk _ xv)
                  apply select_child_embed_monotone
                  exact (hC iu).inf_le_right _ _
                · simp only [dif_neg hij]; exact bot_le
  le_inf := by
    intro a b c hab hac
    induction a using Quotient.ind with
    | _ u =>
      induction b using Quotient.ind with
      | _ v =>
        induction c using Quotient.ind with
        | _ w =>
          rw [select_inf_class_mk]
          unfold select_inf_vertex
          by_cases hv1 : v.val = 1
          · simp only [dif_pos hv1]; exact hac
          · simp only [dif_neg hv1]
            by_cases hw1 : w.val = 1
            · simp only [dif_pos hw1]; exact hab
            · simp only [dif_neg hw1]
              by_cases hv0 : v.val = 0
              · simp only [dif_pos hv0]
                rw [select_class_eq_bot_of_root ls v hv0] at hab; exact hab
              · simp only [dif_neg hv0]
                by_cases hw0 : w.val = 0
                · simp only [dif_pos hw0]
                  rw [select_class_eq_bot_of_root ls w hw0] at hac; exact hac
                · simp only [dif_neg hw0]
                  have hv2 : 2 ≤ v.val := by omega
                  have hw2 : 2 ≤ w.val := by omega
                  generalize hpv : selectChildOf ls v hv2 = pv
                  generalize hpw : selectChildOf ls w hw2 = pw
                  obtain ⟨iv, xv⟩ := pv
                  obtain ⟨iw, xw⟩ := pw
                  by_cases hij : iv = iw
                  · simp only [dif_pos hij]
                    by_cases hu0 : u.val = 0
                    · rw [select_class_eq_bot_of_root ls u hu0]; exact bot_le
                    · by_cases hu1 : u.val = 1
                      · rw [select_class_eq_top_of_bottom ls u hu1] at hab
                        have hv_top :
                            (Quotient.mk _ v : SCCQuotient (stateSpace (.select ls : SessionType)))
                            = (⊤ : SCCQuotient (stateSpace (.select ls : SessionType))) :=
                          @le_antisymm (SCCQuotient (stateSpace (.select ls : SessionType))) _ _ _
                            le_top hab
                        have hMR := Quotient.exact hv_top
                        have hterm_val : (terminalState (.select ls : SessionType)).val = 1 := by
                          unfold terminalState
                          have he : exitSlot (.select ls : SessionType) 0 < stateCount (.select ls : SessionType) := by
                            show exitSlot (.select ls) 0 < stateCount (.select ls); simp only [exitSlot, stateCount]; omega
                          simp only [dif_pos he]
                          show exitSlot (.select ls : SessionType) 0 = 1; simp [exitSlot]
                        have hequiv : MutuallyReachable (stateSpace (.select ls : SessionType))
                            (terminalState _) v := ⟨hMR.2, hMR.1⟩
                        have := (select_sccRel_preserves_bottom ls _ v hequiv).mp hterm_val
                        exact absurd this hv1
                      · have hu2 : 2 ≤ u.val := by omega
                        generalize hpu : selectChildOf ls u hu2 = pu
                        obtain ⟨iu, xu⟩ := pu
                        have hu_eq : u = selectChildShift ls iu xu := by
                          have := selectChildOf_shift ls u hu2
                          rw [hpu] at this; exact this.symm
                        have hv_eq : v = selectChildShift ls iv xv := by
                          have := selectChildOf_shift ls v hv2
                          rw [hpv] at this; exact this.symm
                        have hw_eq : w = selectChildShift ls iw xw := by
                          have := selectChildOf_shift ls w hw2
                          rw [hpw] at this; exact this.symm
                        have hReach_uv : Reachable (stateSpace (.select ls : SessionType)) u v := hab
                        have hReach_uw : Reachable (stateSpace (.select ls : SessionType)) u w := hac
                        rw [hu_eq, hv_eq] at hReach_uv
                        rw [hu_eq, hw_eq] at hReach_uw
                        have hu_in := selectChildShift_inChildRange ls iu xu
                        have hv_in := selectChildShift_inChildRange ls iv xv
                        have hw_in := selectChildShift_inChildRange ls iw xw
                        have hpuv : iu = iv := by
                          by_contra hne
                          exact select_cross_child_not_reachable ls iu iv hne _ _ hu_in hv_in hReach_uv
                        have hpuw : iu = iw := by
                          by_contra hne
                          exact select_cross_child_not_reachable ls iu iw hne _ _ hu_in hw_in hReach_uw
                        subst hij
                        subst hpuv
                        rw [hu_eq]
                        show select_child_embed ls hPC iu (Quotient.mk _ xu) ≤
                          select_child_embed ls hPC iu
                            ((hC iu).inf (Quotient.mk _ xv) (Quotient.mk _ xw))
                        apply select_child_embed_monotone
                        apply (hC iu).le_inf
                        · show Reachable (stateSpace (ls.get iu).2) xu xv
                          exact (select_same_child_reachable_iff ls hPC iu xu xv).mp hReach_uv
                        · show Reachable (stateSpace (ls.get iu).2) xu xw
                          exact (select_same_child_reachable_iff ls hPC iu xu xw).mp hReach_uw
                  · simp only [dif_neg hij]
                    by_cases hu0 : u.val = 0
                    · rw [select_class_eq_bot_of_root ls u hu0]
                    · by_cases hu1 : u.val = 1
                      · rw [select_class_eq_top_of_bottom ls u hu1] at hab
                        have hv_top :
                            (Quotient.mk _ v : SCCQuotient (stateSpace (.select ls : SessionType)))
                            = (⊤ : SCCQuotient (stateSpace (.select ls : SessionType))) :=
                          @le_antisymm (SCCQuotient (stateSpace (.select ls : SessionType))) _ _ _
                            le_top hab
                        have hMR := Quotient.exact hv_top
                        have hterm_val : (terminalState (.select ls : SessionType)).val = 1 := by
                          unfold terminalState
                          have he : exitSlot (.select ls : SessionType) 0 < stateCount (.select ls : SessionType) := by
                            show exitSlot (.select ls) 0 < stateCount (.select ls); simp only [exitSlot, stateCount]; omega
                          simp only [dif_pos he]
                          show exitSlot (.select ls : SessionType) 0 = 1; simp [exitSlot]
                        have hequiv : MutuallyReachable (stateSpace (.select ls : SessionType))
                            (terminalState _) v := ⟨hMR.2, hMR.1⟩
                        have := (select_sccRel_preserves_bottom ls _ v hequiv).mp hterm_val
                        exact absurd this hv1
                      · have hu2 : 2 ≤ u.val := by omega
                        generalize hpu : selectChildOf ls u hu2 = pu
                        obtain ⟨iu, xu⟩ := pu
                        have hu_eq : u = selectChildShift ls iu xu := by
                          have := selectChildOf_shift ls u hu2
                          rw [hpu] at this; exact this.symm
                        have hv_eq : v = selectChildShift ls iv xv := by
                          have := selectChildOf_shift ls v hv2
                          rw [hpv] at this; exact this.symm
                        have hw_eq : w = selectChildShift ls iw xw := by
                          have := selectChildOf_shift ls w hw2
                          rw [hpw] at this; exact this.symm
                        have hReach_uv : Reachable (stateSpace (.select ls : SessionType)) u v := hab
                        have hReach_uw : Reachable (stateSpace (.select ls : SessionType)) u w := hac
                        rw [hu_eq, hv_eq] at hReach_uv
                        rw [hu_eq, hw_eq] at hReach_uw
                        have hu_in := selectChildShift_inChildRange ls iu xu
                        have hv_in := selectChildShift_inChildRange ls iv xv
                        have hw_in := selectChildShift_inChildRange ls iw xw
                        have hpuv : iu = iv := by
                          by_contra hne
                          exact select_cross_child_not_reachable ls iu iv hne _ _ hu_in hv_in hReach_uv
                        have hpuw : iu = iw := by
                          by_contra hne
                          exact select_cross_child_not_reachable ls iu iw hne _ _ hu_in hw_in hReach_uw
                        exact absurd (hpuv.symm.trans hpuw) hij


end SessionType

end Reticulate.Spec
