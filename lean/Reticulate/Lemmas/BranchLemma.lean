/-
Copyright (c) 2026 Alexandre Zua Caldeira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexandre Zua Caldeira
-/
import Reticulate.Graph.SCC
import Mathlib.Order.ModularLattice

/-!
# Branch Lemma (External Choice)

Proves that adding a new top element to a finite collection of bounded lattices
that share a common bottom produces a bounded lattice.

This models the session type constructor `&{m₁: S₁, ..., mₙ: Sₙ}`:
the state space L(&{m₁:S₁,...}) has a new top state (the branch point) with
transitions to the top of each L(Sᵢ), and all L(Sᵢ) share a common bottom (end).

## The construction

Given: A finite directed graph G with a distinguished `root` vertex such that:
1. Removing `root`, the graph decomposes into connected components C₁,...,Cₙ.
2. Each component's SCC quotient is a bounded lattice.
3. All components share a common bottom vertex `bot`.
4. Root has edges to each component's top and no other outgoing edges.
5. Root has no incoming edges (it is the unique source).

Then: `SCCQuotient G` is a bounded lattice.

## Simplified approach

Rather than the full decomposition, we prove the key structural lemma:
adding a new minimum (in our reachability ordering, this is the root
which reaches everything) to a bounded lattice preserves lattice structure.
This is because the root becomes the new ⊥ and all meets/joins are preserved.

Actually, the branching case reduces to the Bottom Absorption Lemma in reverse:
the root is a new element below everything. We formalise this as a general
lattice-theoretic result.

## Main result

* `top_extension_lattice`: Given a bounded lattice L and a new top element ⊤'
  above everything, the extended poset L ∪ {⊤'} is a bounded lattice.

Note: In our reachability convention ([u] ≤ [v] iff u reaches v), the branch
root is the BOTTOM (it reaches all components). So what we actually need is
a bottom extension. But by duality, top and bottom extensions are equivalent.
We prove the bottom extension directly since that matches our convention.
-/

open Classical
noncomputable section

namespace Reticulate.BranchLemma

variable {α : Type*} [Lattice α] [OrderTop α]

/-- The extended type: the original lattice plus a new bottom element. -/
inductive WithBot' (α : Type*) where
  | newBot : WithBot' α
  | old (x : α) : WithBot' α

namespace WithBot'

variable {α : Type*} [Lattice α] [OrderTop α]

/-- Ordering: newBot ≤ everything; old a ≤ old b iff a ≤ b. -/
protected def le (x y : WithBot' α) : Prop :=
  match x, y with
  | .newBot, _ => True
  | .old _, .newBot => False
  | .old a, .old b => a ≤ b

protected def lt (x y : WithBot' α) : Prop :=
  WithBot'.le x y ∧ ¬WithBot'.le y x

instance : LE (WithBot' α) where le := WithBot'.le
instance : LT (WithBot' α) where lt := WithBot'.lt

set_option linter.unusedSectionVars false in
@[simp] theorem newBot_le (y : WithBot' α) : WithBot'.newBot ≤ y := trivial
set_option linter.unusedSectionVars false in
@[simp] theorem old_not_le_newBot (a : α) : ¬(WithBot'.old a ≤ (WithBot'.newBot : WithBot' α)) := id
set_option linter.unusedSectionVars false in
@[simp] theorem old_le_old {a b : α} : (WithBot'.old a ≤ WithBot'.old b) ↔ a ≤ b := Iff.rfl

instance : PartialOrder (WithBot' α) where
  le_refl x := by cases x <;> simp
  le_trans := by
    intro x y z hxy hyz
    match x, y, z with
    | .newBot, _, _ => trivial
    | .old _, .newBot, _ => exact absurd hxy (by simp)
    | .old _, .old _, .newBot => exact absurd hyz (by simp)
    | .old a, .old b, .old c => exact le_trans (α := α) hxy hyz
  le_antisymm := by
    intro x y hxy hyx
    match x, y with
    | .newBot, .newBot => rfl
    | .newBot, .old _ => exact absurd hyx (by simp)
    | .old _, .newBot => exact absurd hxy (by simp)
    | .old a, .old b =>
      have := le_antisymm (α := α) hxy hyx
      subst this; rfl
  lt := WithBot'.lt

instance : OrderBot (WithBot' α) where
  bot := .newBot
  bot_le _ := trivial

instance : OrderTop (WithBot' α) where
  top := .old ⊤
  le_top x := by cases x with | newBot => trivial | old a => exact le_top (α := α)

/-- Join in the extended type. -/
private def sup' (x y : WithBot' α) : WithBot' α :=
  match x, y with
  | .newBot, y => y
  | x, .newBot => x
  | .old a, .old b => .old (a ⊔ b)

/-- Meet in the extended type. -/
private def inf' (x y : WithBot' α) : WithBot' α :=
  match x, y with
  | .newBot, _ => .newBot
  | _, .newBot => .newBot
  | .old a, .old b => .old (a ⊓ b)

/-- The extended type with a new bottom forms a lattice. -/
instance : Lattice (WithBot' α) where
  sup := sup'
  le_sup_left := by
    intro x y; match x, y with
    | .newBot, _ => trivial
    | .old _, .newBot => exact le_refl _
    | .old a, .old b => show a ≤ a ⊔ b; exact _root_.le_sup_left
  le_sup_right := by
    intro x y; match x, y with
    | .newBot, _ => exact le_refl _
    | .old _, .newBot => trivial
    | .old a, .old b => show b ≤ a ⊔ b; exact _root_.le_sup_right
  sup_le := by
    intro x y z hxz hyz
    match x, y, z with
    | .newBot, _, _ => exact hyz
    | .old _, .newBot, _ => exact hxz
    | .old _, .old _, .newBot => exact absurd hxz (by simp)
    | .old a, .old b, .old c =>
      show a ⊔ b ≤ c; exact _root_.sup_le hxz hyz
  inf := inf'
  inf_le_left := by
    intro x y; match x, y with
    | .newBot, _ => trivial
    | .old _, .newBot => trivial
    | .old a, .old b => show a ⊓ b ≤ a; exact _root_.inf_le_left
  inf_le_right := by
    intro x y; match x, y with
    | .newBot, _ => trivial
    | .old _, .newBot => trivial
    | .old a, .old b => show a ⊓ b ≤ b; exact _root_.inf_le_right
  le_inf := by
    intro x y z hxy hxz
    match y, z with
    | .newBot, _ =>
      match x with
      | .newBot => trivial
      | .old _ => exact absurd hxy (by simp)
    | _, .newBot =>
      match x with
      | .newBot => trivial
      | .old _ => exact absurd hxz (by simp)
    | .old a, .old b =>
      match x with
      | .newBot => trivial
      | .old c => show c ≤ a ⊓ b; exact _root_.le_inf hxy hxz

instance : BoundedOrder (WithBot' α) where
  bot := .newBot
  bot_le := fun _ => trivial
  top := .old ⊤
  le_top := fun x => by cases x with | newBot => trivial | old a => exact le_top (α := α)

/-- **Branch Lemma**: Adding a new bottom to a bounded lattice with a top
    produces a bounded lattice.

    In session-type terms: the branch root (which reaches all sub-state-spaces)
    becomes the new ⊥ in the reachability ordering, and the resulting
    poset is a bounded lattice. -/
theorem branch_preserves_lattice :
    ∃ (_ : Lattice (WithBot' α)) (_ : OrderBot (WithBot' α)) (_ : OrderTop (WithBot' α)), True :=
  ⟨inferInstance, inferInstance, inferInstance, trivial⟩

/-! ### Sup / inf reduction lemmas

Simp lemmas that unfold `⊔` and `⊓` on `WithBot'` against
specific constructor combinations. These are the key lemmas
that make downstream proofs about `WithBot'`'s lattice-
theoretic behaviour (e.g. `DistribLattice` in
`ModularityClassification.lean`) tractable without having to
pattern-match on private `sup'` / `inf'` defs. -/

@[simp] theorem newBot_sup (y : WithBot' α) :
    (WithBot'.newBot : WithBot' α) ⊔ y = y := rfl

@[simp] theorem sup_newBot (x : WithBot' α) :
    x ⊔ (WithBot'.newBot : WithBot' α) = x := by
  cases x with
  | newBot => rfl
  | old _ => rfl

@[simp] theorem old_sup_old (a b : α) :
    (WithBot'.old a : WithBot' α) ⊔ WithBot'.old b = WithBot'.old (a ⊔ b) :=
  rfl

@[simp] theorem newBot_inf (y : WithBot' α) :
    (WithBot'.newBot : WithBot' α) ⊓ y = WithBot'.newBot := rfl

@[simp] theorem inf_newBot (x : WithBot' α) :
    x ⊓ (WithBot'.newBot : WithBot' α) = WithBot'.newBot := by
  cases x with
  | newBot => rfl
  | old _ => rfl

@[simp] theorem old_inf_old (a b : α) :
    (WithBot'.old a : WithBot' α) ⊓ WithBot'.old b = WithBot'.old (a ⊓ b) :=
  rfl

/-! ### DecidableEq and Fintype

Required by `Reticulate.StateSpaceFinite` so that the T2b `.chain`
case of `stateSpaceDecEq` / `stateSpaceFintype` can delegate to
`WithBot' α` instances. -/

instance [DecidableEq α] : DecidableEq (WithBot' α)
  | .newBot, .newBot => isTrue rfl
  | .newBot, .old _  => isFalse (by intro h; cases h)
  | .old _,  .newBot => isFalse (by intro h; cases h)
  | .old a,  .old b  =>
      if h : a = b then isTrue (by rw [h])
      else isFalse (by intro heq; cases heq; exact h rfl)

instance [Fintype α] : Fintype (WithBot' α) where
  elems := {WithBot'.newBot} ∪ (Finset.univ.image WithBot'.old)
  complete x := by
    cases x with
    | newBot => simp
    | old a  =>
        simp only [Finset.mem_union, Finset.mem_singleton,
                   Finset.mem_image, Finset.mem_univ, true_and]
        exact Or.inr ⟨a, rfl⟩

end WithBot'

end Reticulate.BranchLemma

/-! ### DistribLattice instance on WithBot'

If `α` is a distributive bounded lattice (with a top), then
`Reticulate.BranchLemma.WithBot' α` is also distributive.
Declared outside the main `Reticulate.BranchLemma.WithBot'`
namespace (which has a `variable [Lattice α] [OrderTop α]`
binding that collides with the `DistribLattice α` type-class
parameter) and in its own noncomputable section.

Uses the simp lemmas `newBot_sup`/`old_sup_old`/etc. to reduce
each of the 8 constructor cases to a facts about `α`'s
distributive law. -/

namespace Reticulate.BranchLemma.WithBot'

open Reticulate.BranchLemma

instance instDistribLattice
    {α : Type*} [DistribLattice α] [OrderTop α] :
    DistribLattice (WithBot' α) :=
  -- Reuse the existing `Lattice (WithBot' α)` instance via
  -- `inferInstance` to avoid the typeclass diamond that arises
  -- when downstream proofs mix this DistribLattice with the
  -- pre-existing Lattice (the `where` constructor would
  -- synthesise a NEW Lattice, distinct from the original).
  { (inferInstance : Lattice (WithBot' α)) with
    le_sup_inf := by
      intro x y z
      match x, y, z with
      | .newBot, .newBot, .newBot => simp
      | .newBot, .newBot, .old _  => simp
      | .newBot, .old _, .newBot  => simp
      | .newBot, .old b, .old c   => simp
      | .old _, .newBot, .newBot  => simp
      | .old a, .newBot, .old c   => simp
      | .old a, .old b, .newBot   => simp
      | .old a, .old b, .old c    =>
          simp
          exact DistribLattice.le_sup_inf a b c }

/-- **`IsModularLattice (WithBot' α)`** — direct form,
    parameterised by `[IsModularLattice α]` rather than
    `[DistribLattice α]`.

    v12-Lean: this instance lets `T2b_DF` propagate
    `IsModularLattice (stateSpace s)` through recursion without
    touching `DistribLattice`. Since `IsModularLattice` is a
    Prop class that does NOT extend `Lattice`, installing it
    via `haveI` doesn't introduce a rival `toLattice`
    projection, so the v11-Lean typeclass diamond simply
    doesn't arise.

    Proof: 8 cases on `(x, y, z)` constructors. When `x ≤ z`
    forces `x = .newBot` or both are `.old`, each case
    reduces to either a trivial inequality (newBot-heavy) or
    to `α`'s own modular identity. -/
instance instIsModularLattice
    {α : Type*} [Lattice α] [OrderTop α] [IsModularLattice α] :
    IsModularLattice (WithBot' α) where
  sup_inf_le_assoc_of_le := by
    intro x y z hxz
    -- Valid (x, z) shapes: (newBot, newBot), (newBot, old),
    -- (old, old) with the inner `a ≤ c` from `hxz`. The
    -- (old, newBot) case is impossible because `old a ≤ newBot`
    -- unfolds to False.
    match x, y, z with
    -- (x = newBot, any y, any z): LHS collapses to a
    -- newBot-containing meet; all cases reduce trivially.
    | .newBot, .newBot, .newBot => simp
    | .newBot, .newBot, .old _  => simp
    | .newBot, .old _, .newBot  => simp
    | .newBot, .old _, .old _   => simp
    -- (x = old, z = newBot): impossible via hxz.
    | .old _, _, .newBot => exact (hxz : False).elim
    -- (x = old a, z = old c) with a ≤ c from hxz:
    | .old a, .newBot, .old c =>
        -- LHS = (old a ⊔ newBot) ⊓ old c = old a ⊓ old c
        --     = old (a ⊓ c)
        -- RHS = old a ⊔ (newBot ⊓ old c) = old a ⊔ newBot
        --     = old a
        -- Need: old (a ⊓ c) ≤ old a, i.e. a ⊓ c ≤ a.
        simp
    | .old a, .old b, .old c =>
        -- LHS = (old a ⊔ old b) ⊓ old c = old ((a ⊔ b) ⊓ c)
        -- RHS = old a ⊔ (old b ⊓ old c) = old (a ⊔ (b ⊓ c))
        -- Need the modular identity on α, using `a ≤ c`.
        have ha : a ≤ c := hxz
        have hα : (a ⊔ b) ⊓ c ≤ a ⊔ (b ⊓ c) :=
          IsModularLattice.sup_inf_le_assoc_of_le b ha
        simp
        exact old_le_old.mpr hα

end Reticulate.BranchLemma.WithBot'

end
