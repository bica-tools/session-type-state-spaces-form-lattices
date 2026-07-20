/-
Copyright (c) 2026 Alexandre Zua Caldeira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexandre Zua Caldeira
-/
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.UpperLower.Basic

/-!
# Bottom Absorption Lemma

A general lattice-theoretic result: collapsing a downward-closed set containing ⊥
into a single bottom element preserves bounded lattice structure.

This formalizes Lemma 5 from "Session Type State Spaces Form Lattices"
(Caldeira & Vasconcelos, 2026).

## Main result

* `BottomAbsorption.bottom_absorption`: Given a bounded lattice `(L, ≤)` and
  a downward-closed set `D ⊆ L` with `⊥ ∈ D` and `⊤ ∉ D`, the quotient type
  `L'` admits a bounded lattice structure.
-/

open Classical
noncomputable section

namespace BottomAbsorption

variable {α : Type*} [Lattice α] [BoundedOrder α]

/-- Hypotheses for the absorption lemma. -/
structure DownwardClosedBot (D : Set α) : Prop where
  bot_mem : ⊥ ∈ D
  lower_closed : IsLowerSet D
  top_not_mem : ⊤ ∉ D

/-- The quotient type: either a survivor (element not in D) or the new bottom.
    We use an inductive to avoid inheriting `Option`'s instances. -/
inductive L' (D : Set α) where
  /-- The new bottom element (collapsed D). -/
  | bot' : L' D
  /-- A survivor: an element of L not in D. -/
  | surv (x : α) (hx : x ∉ D) : L' D

namespace L'

set_option linter.unusedSectionVars false

variable {D : Set α}

/-- Ordering on L': bot' ≤ everything; surv a _ ≤ surv b _ iff a ≤ b in L. -/
protected def le (x y : L' D) : Prop :=
  match x, y with
  | .bot', _ => True
  | .surv _ _, .bot' => False
  | .surv a _, .surv b _ => a ≤ b

/-- Strict ordering. -/
protected def lt (x y : L' D) : Prop :=
  L'.le x y ∧ ¬L'.le y x

instance : LE (L' D) where le := L'.le
instance : LT (L' D) where lt := L'.lt

@[simp] theorem bot'_le (y : L' D) : L'.bot' ≤ y := trivial

@[simp] theorem surv_not_le_bot' (a : α) (ha : a ∉ D) :
    ¬(L'.surv a ha ≤ (L'.bot' : L' D)) := id

@[simp] theorem surv_le_surv {a b : α} {ha : a ∉ D} {hb : b ∉ D} :
    (L'.surv a ha ≤ L'.surv b hb) ↔ a ≤ b := Iff.rfl

theorem lt_iff_le_not_le {x y : L' D} :
    x < y ↔ x ≤ y ∧ ¬y ≤ x := Iff.rfl

-- ---- PartialOrder ----------------------------------------------------

instance : PartialOrder (L' D) where
  le_refl x := by cases x <;> simp
  le_trans := by
    intro x y z hxy hyz
    match x, y, z with
    | .bot', _, _ => trivial
    | .surv _ _, .bot', _ => exact absurd hxy (by simp)
    | .surv _ _, .surv _ _, .bot' => exact absurd hyz (by simp)
    | .surv a _, .surv b _, .surv c _ =>
      exact le_trans (α := α) hxy hyz
  le_antisymm := by
    intro x y hxy hyx
    match x, y with
    | .bot', .bot' => rfl
    | .bot', .surv _ _ => exact absurd hyx (by simp)
    | .surv _ _, .bot' => exact absurd hxy (by simp)
    | .surv a ha, .surv b hb =>
      have := le_antisymm (α := α) hxy hyx
      subst this; rfl
  lt := L'.lt

-- ---- OrderBot and OrderTop -------------------------------------------

instance : OrderBot (L' D) where
  bot := .bot'
  bot_le _ := trivial

def mkOrderTop (hD : DownwardClosedBot D) : OrderTop (L' D) where
  top := .surv ⊤ hD.top_not_mem
  le_top x := by
    cases x with
    | bot' => trivial
    | surv a _ => exact le_top (α := α)

-- ---- Sup (join) ------------------------------------------------------

private def sup_val (hD : DownwardClosedBot D) (x y : L' D) : L' D :=
  match x, y with
  | .bot', y => y
  | x, .bot' => x
  | .surv a ha, .surv b _ =>
    .surv (a ⊔ b) (fun h => ha (hD.lower_closed le_sup_left h))

-- ---- Inf (meet) — the key case ------------------------------------

private def inf_val (x y : L' D) : L' D :=
  match x, y with
  | .bot', _ => .bot'
  | _, .bot' => .bot'
  | .surv a _, .surv b _ =>
    if h : a ⊓ b ∉ D then .surv (a ⊓ b) h
    else .bot'

-- ---- Lattice ---------------------------------------------------------

def mkLattice (hD : DownwardClosedBot D) : Lattice (L' D) where
  sup := sup_val hD
  le_sup_left := by
    intro x y
    match x, y with
    | .bot', _ => trivial
    | .surv _ _, .bot' => exact le_refl _
    | .surv a _, .surv b _ =>
      show a ≤ a ⊔ b; exact le_sup_left
  le_sup_right := by
    intro x y
    match x, y with
    | .bot', _ => exact le_refl _
    | .surv _ _, .bot' => trivial
    | .surv a _, .surv b _ =>
      show b ≤ a ⊔ b; exact le_sup_right
  sup_le := by
    intro x y z hxz hyz
    match x, y, z with
    | .bot', _, _ => exact hyz
    | .surv _ _, .bot', _ => exact hxz
    | .surv a _, .surv b _, .bot' => exact absurd hxz (by simp)
    | .surv a _, .surv b _, .surv c _ =>
      show a ⊔ b ≤ c; exact _root_.sup_le hxz hyz
  inf := inf_val
  inf_le_left := by
    intro x y
    match x, y with
    | .bot', _ => trivial
    | .surv _ _, .bot' => trivial
    | .surv a ha, .surv b hb =>
      show inf_val (.surv a ha) (.surv b hb) ≤ .surv a ha
      simp only [inf_val]
      split
      · show a ⊓ b ≤ a; exact inf_le_left
      · trivial
  inf_le_right := by
    intro x y
    match x, y with
    | .bot', _ => trivial
    | .surv _ _, .bot' => trivial
    | .surv a ha, .surv b hb =>
      show inf_val (.surv a ha) (.surv b hb) ≤ .surv b hb
      simp only [inf_val]
      split
      · show a ⊓ b ≤ b; exact inf_le_right
      · trivial
  le_inf := by
    intro x y z hxy hxz
    match y, z with
    | .bot', _ =>
      match x with
      | .bot' => trivial
      | .surv _ _ => exact absurd hxy (by simp)
    | _, .bot' =>
      match x with
      | .bot' => trivial
      | .surv _ _ => exact absurd hxz (by simp)
    | .surv a ha, .surv b hb =>
      match x with
      | .bot' => trivial
      | .surv c hc =>
        -- c ≤ a and c ≤ b, so c ≤ a ⊓ b in L
        have hca : c ≤ a := hxy
        have hcb : c ≤ b := hxz
        have hc_le_inf : c ≤ a ⊓ b := _root_.le_inf hca hcb
        show (.surv c hc) ≤ inf_val (.surv a ha) (.surv b hb)
        simp only [inf_val]
        split
        · -- a ⊓ b ∉ D: meet preserved
          show c ≤ a ⊓ b; exact hc_le_inf
        · -- a ⊓ b ∈ D: any survivor c ≤ a ⊓ b ∈ D means c ∈ D (contradiction)
          rename_i h_in_D
          push_neg at h_in_D
          exact absurd (hD.lower_closed hc_le_inf h_in_D) hc

/-- **Bottom Absorption Lemma** (Lemma 5).

    Given a bounded lattice `(L, ≤)` with a downward-closed set `D` containing ⊥
    but not ⊤, the quotient `L' = (L \ D) ∪ {⊥'}` carries a bounded lattice
    structure. -/
theorem bottom_absorption (D : Set α) (hD : DownwardClosedBot D) :
    ∃ (_ : Lattice (L' D)) (_ : OrderBot (L' D)) (_ : OrderTop (L' D)), True :=
  ⟨mkLattice hD, inferInstance, mkOrderTop hD, trivial⟩

end L'

end BottomAbsorption

end
