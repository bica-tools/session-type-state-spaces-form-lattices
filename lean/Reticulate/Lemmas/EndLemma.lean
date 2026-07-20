/-
Copyright (c) 2026 Alexandre Zua Caldeira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexandre Zua Caldeira
-/
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.Fintype.Basic

/-!
# End Lemma: L(end) Is a Bounded Lattice

The session type `end` denotes a terminated session. Its state space L(end)
consists of a single state q₀ (the terminal state). A singleton poset is
trivially a bounded lattice: q₀ is both ⊤ and ⊥, and every meet/join is q₀.

This is Lemma 3 (End) in the ICE 2026 paper, and the base case of the
structural induction proving the Reticulate Theorem.

## Main result

* `end_bounded_lattice` : The singleton type (modeling L(end)) is a bounded lattice.
-/

namespace Reticulate.EndLemma

/-- The state space of `end`: a single terminal state. -/
inductive EndState : Type where
  | q₀
  deriving DecidableEq, Repr

instance : Fintype EndState where
  elems := {EndState.q₀}
  complete := by intro x; cases x; simp

open EndState

/-- Every EndState is q₀. -/
theorem EndState.unique (x : EndState) : x = q₀ := by
  cases x; rfl

/-- Ordering on the singleton: q₀ ≤ q₀. -/
protected def EndState.le : EndState → EndState → Prop
  | q₀, q₀ => True

instance : LE EndState where le := EndState.le

instance : DecidableRel (· ≤ · : EndState → EndState → Prop) := by
  intro a b; cases a <;> cases b <;> simp [LE.le, EndState.le] <;> exact inferInstance

instance : PartialOrder EndState where
  le_refl := by intro x; cases x; trivial
  le_trans := by intro x y z _ _; cases x <;> cases y <;> cases z <;> trivial
  le_antisymm := by intro x y _ _; cases x <;> cases y; rfl

instance : Lattice EndState where
  sup := fun _ _ => q₀
  le_sup_left := by intro a b; cases a <;> cases b; trivial
  le_sup_right := by intro a b; cases a <;> cases b; trivial
  sup_le := by intro a b c _ _; cases a <;> cases b <;> cases c; trivial
  inf := fun _ _ => q₀
  inf_le_left := by intro a b; cases a <;> cases b; trivial
  inf_le_right := by intro a b; cases a <;> cases b; trivial
  le_inf := by intro a b c _ _; cases a <;> cases b <;> cases c; trivial

instance : OrderBot EndState where
  bot := q₀
  bot_le := by intro a; cases a; trivial

instance : OrderTop EndState where
  top := q₀
  le_top := by intro a; cases a; trivial

instance : BoundedOrder EndState where
  __ := inferInstanceAs (OrderBot EndState)
  __ := inferInstanceAs (OrderTop EndState)

/-- `EndState` is a distributive lattice (singleton lattices
    trivially satisfy every lattice identity). This instance
    is used by `Reticulate.ModularityClassification.T2b_DF`
    to close the `.end_` base case via the Mathlib priority
    instance `DistribLattice → IsModularLattice`. Uses the
    `{ inferInstance with ... }` pattern to reuse the
    existing `Lattice EndState` and avoid a typeclass diamond. -/
instance : DistribLattice EndState :=
  { (inferInstance : Lattice EndState) with
    le_sup_inf := by
      intro x y z
      -- Every element of `EndState` is `q₀` (singleton type).
      have hx := EndState.unique x
      have hy := EndState.unique y
      have hz := EndState.unique z
      subst hx; subst hy; subst hz
      exact le_refl _ }

/-- **End Lemma**: L(end) is a bounded lattice.

    The state space of `end` has a single state q₀. The singleton poset
    {q₀} with q₀ ≤ q₀ is trivially a bounded lattice where q₀ = ⊤ = ⊥
    and all meets and joins equal q₀. -/
theorem end_bounded_lattice :
    ∃ (_ : Lattice EndState) (_ : BoundedOrder EndState), True :=
  ⟨inferInstance, inferInstance, trivial⟩

end Reticulate.EndLemma
