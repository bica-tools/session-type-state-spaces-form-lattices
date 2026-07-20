/-
Copyright (c) 2026 Alexandre Zua Caldeira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexandre Zua Caldeira
-/
import Mathlib.Order.BoundedOrder.Basic

/-!
# Unique Extrema: Bounded Lattices Have Unique Top and Bottom

**Proposition (Unique Extrema)**: For every well-formed session type S,
L(S)/≡ has a unique initial state q_⊤ that reaches all states, and a
unique terminal state q_⊥ reachable from all states.

In lattice-theoretic terms: every bounded lattice has a unique top element
(greatest element) and a unique bottom element (least element).

In session-type terms:
- q_⊤ = initial state (the protocol starting point that reaches everything)
- q_⊥ = terminal state (the end state reachable from everything)

## Main results

* `unique_top` : ⊤ is the unique greatest element.
* `unique_bot` : ⊥ is the unique least element.
* `unique_extrema` : Both extrema exist and are unique.
-/

namespace Reticulate.UniqueExtrema

variable {α : Type*} [PartialOrder α]

/-- **Unique Top**: In a bounded order, there is exactly one greatest element.
    If some element t satisfies ∀ x, x ≤ t, then t = ⊤. -/
theorem unique_top [OrderTop α] (t : α) (ht : ∀ (x : α), x ≤ t) : t = ⊤ :=
  le_antisymm le_top (ht ⊤)

/-- **Unique Bottom**: In a bounded order, there is exactly one least element.
    If some element b satisfies ∀ x, b ≤ x, then b = ⊥. -/
theorem unique_bot [OrderBot α] (b : α) (hb : ∀ (x : α), b ≤ x) : b = ⊥ :=
  le_antisymm (hb ⊥) bot_le

/-- **Proposition (Unique Extrema)**: Every bounded lattice has a unique top
    and a unique bottom.

    For session types: L(S)/≡ has a unique initial state (⊤ in reachability
    ordering — reaches everything) and a unique terminal state (⊥ — reachable
    from everything).

    Uniqueness means: any other element with the same universal property
    must equal the extremum. -/
theorem unique_extrema [BoundedOrder α] :
    (∀ (t : α), (∀ (x : α), x ≤ t) → t = ⊤) ∧
    (∀ (b : α), (∀ (x : α), b ≤ x) → b = ⊥) :=
  ⟨fun t ht => unique_top t ht, fun b hb => unique_bot b hb⟩

/-- Top is characterized by its universal property. -/
theorem top_iff_ge_all [OrderTop α] (t : α) : t = ⊤ ↔ ∀ (x : α), x ≤ t := by
  constructor
  · intro h; subst h; exact fun x => le_top
  · exact unique_top t

/-- Bottom is characterized by its universal property. -/
theorem bot_iff_le_all [OrderBot α] (b : α) : b = ⊥ ↔ ∀ (x : α), b ≤ x := by
  constructor
  · intro h; subst h; exact fun x => bot_le
  · exact unique_bot b

end Reticulate.UniqueExtrema
