/-
Copyright (c) 2026 Alexandre Zua Caldeira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexandre Zua Caldeira
-/
import Reticulate.Graph.Reachability

/-!
# The SCC quotient and its partial order

Collapse a finite directed graph by mutual reachability — that is,
identify two vertices when each can reach the other — and the
resulting set inherits a partial order from reachability. This
module performs that collapse and proves that the inherited order
is reflexive, transitive, and antisymmetric.

This is the construction the paper calls
"$\mathcal{L}(S)/{\equiv}$" in §3 of ICE 2026 and uses
`def:scc-quotient` for. Every lattice statement about
session-type state spaces lives on this quotient — not on the raw
graph — because antisymmetry only emerges after SCCs are merged.

What is exported.
* `SCCSetoid G` — the setoid (equivalence relation) on the
  vertices of `G` whose equivalence is mutual reachability.
* `SCCQuotient G` — the quotient type `V / ≈`. Each element
  represents one strongly-connected component of `G`.
* `SCCQuotient.le'` — the order on the quotient: `[u] ≤ [v]`
  iff `u` can reach `v`. Well-defined because mutual reachability
  preserves reachability.
* `SCCQuotient.instPartialOrder` — the partial order on the
  quotient (`prop:reach-preorder` becomes a partial order *after*
  quotienting, paper §3 / `prop:extrema` adjacent).

Conceptual dependencies.
* `Reticulate.Reachability` for `Reachable`, `MutuallyReachable`,
  and the equivalence-relation packaging.
* Mathlib's `Quotient`, `Setoid`, and `PartialOrder` typeclass.
-/

namespace Reticulate

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The setoid on `V` whose equivalence is mutual reachability:
`u ≈ v` iff `u` and `v` can each reach the other in `G`.

This is the data needed to take a quotient: a relation plus a proof
it is an equivalence. The proof comes from
`mutuallyReachable_equivalence` in `Reticulate.Reachability`. Used
exclusively as the setoid argument to `Quotient` in `SCCQuotient`. -/
def SCCSetoid (G : FinDiGraph V) : Setoid V where
  r := MutuallyReachable G
  iseqv := mutuallyReachable_equivalence G

/-- The SCC quotient of `G`: the type whose elements are
equivalence classes `[u]` of mutually reachable vertices.

Intuitively, this is the graph after every strongly-connected
component is collapsed to a single point. It is the carrier of the
"lattice" promised by the Reticulate Theorem (`thm:reticulate`).
For example, on a graph with two vertices `u, v` and edges
`u -> v, v -> u`, `SCCQuotient` has just one element. -/
def SCCQuotient (G : FinDiGraph V) := Quotient (SCCSetoid G)

namespace SCCQuotient

variable (G : FinDiGraph V)

/-- The order on `SCCQuotient G`: `[u] ≤ [v]` iff `u` reaches `v`
in `G`.

This corresponds to `def:quotient-order` in the paper: reachability
descends from the original graph to the quotient. The
well-definedness check is the inner `propext` block: if `u₁ ≈ u₂`
and `v₁ ≈ v₂`, then `Reachable u₁ v₁ ↔ Reachable u₂ v₂`, because
each side can be turned into the other by chaining through the
mutual-reachability witnesses. Proof technique: pre- and
post-compose the path with the SCC equivalence paths. -/
def le' : SCCQuotient G → SCCQuotient G → Prop :=
  Quotient.lift₂
    (fun u v => Reachable G u v)
    (fun u₁ v₁ u₂ v₂ (hu : MutuallyReachable G u₁ u₂) (hv : MutuallyReachable G v₁ v₂) => by
      apply propext
      constructor
      · intro h
        exact Reachable.trans G hu.2 (Reachable.trans G h hv.1)
      · intro h
        exact Reachable.trans G hu.1 (Reachable.trans G h hv.2))

/-- Hook the lifted `le'` predicate into Lean's `≤` notation on
`SCCQuotient G`. Every downstream `≤`-statement about SCC quotients
unfolds to this. -/
instance instLE : LE (SCCQuotient G) where
  le := le' G

/-- Reflexivity of the quotient order: `[u] ≤ [u]` follows from
`Reachable.refl`. Proof technique: induct on the quotient class to
get a representative, then use reflexivity of reachability. -/
private theorem le_refl' (x : SCCQuotient G) : x ≤ x := by
  induction x using Quotient.ind with
  | _ u => exact Reachable.refl G u

/-- Transitivity of the quotient order. Proof technique: induct on
all three quotient classes to obtain representatives, then chain
reachability through the middle representative. -/
private theorem le_trans' (x y z : SCCQuotient G) : x ≤ y → y ≤ z → x ≤ z := by
  induction x using Quotient.ind with
  | _ u =>
    induction y using Quotient.ind with
    | _ v =>
      induction z using Quotient.ind with
      | _ w =>
        intro huv hvw
        exact Reachable.trans G huv hvw

/-- Antisymmetry: if `[u] ≤ [v]` and `[v] ≤ [u]` (i.e. each reaches
the other) then they are *equal* SCC classes. This is the property
that fails on the raw graph and is the whole reason we quotient.

Proof technique: induct on both classes to get representatives `u`,
`v`; the two reachability hypotheses bundle to a `MutuallyReachable`
pair; then `Quotient.sound` collapses them to the same class. -/
private theorem le_antisymm' (x y : SCCQuotient G) : x ≤ y → y ≤ x → x = y := by
  induction x using Quotient.ind with
  | _ u =>
    induction y using Quotient.ind with
    | _ v =>
      intro huv hvu
      exact Quotient.sound ⟨huv, hvu⟩

/-- **The SCC quotient with reachability ordering is a partial order.**

Bundling the three previous lemmas gives Lean a `PartialOrder`
typeclass instance on `SCCQuotient G`. Once we have this, all of
Mathlib's order-theoretic vocabulary (`Lattice`, `BoundedOrder`,
`OrderEmbedding`, …) is available on the quotient.

This corresponds to the unnamed observation just before
`prop:extrema` in §3 of the paper: reachability gives a partial
order on the quotient. -/
instance instPartialOrder : PartialOrder (SCCQuotient G) where
  le_refl := le_refl' G
  le_trans := le_trans' G
  le_antisymm := le_antisymm' G

end SCCQuotient

end Reticulate
