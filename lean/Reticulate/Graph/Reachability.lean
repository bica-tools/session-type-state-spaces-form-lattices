/-
Copyright (c) 2026 Alexandre Zua Caldeira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexandre Zua Caldeira
-/
import Reticulate.Graph.DirectedGraph
import Mathlib.Order.RelClasses
import Mathlib.Logic.Relation

/-!
# Reachability and mutual reachability

This module turns the bare edge relation of a `FinDiGraph` into the
"can `u` get to `v` by following edges?" relation, and the symmetric
"`u` and `v` can each reach the other" relation. These are the
ingredients out of which the SCC quotient — and ultimately the
lattice on a session-type state space — is constructed.

What is exported.
* `Reachable G u v` — there is a directed path from `u` to `v` in
  `G`, possibly of length zero.
* `MutuallyReachable G u v` — both `Reachable G u v` and
  `Reachable G v u` hold; equivalently, `u` and `v` lie in the same
  strongly-connected component.
* `mutuallyReachable_equivalence` — mutual reachability is an
  equivalence relation.

Why we need this. The paper's lattice `\mathcal{L}(S)/\equiv`
(see §3 of ICE 2026) is the SCC quotient of the state space of `S`,
ordered by reachability. To define that quotient and show it is a
partial order (let alone a lattice) we first need (a) reachability
as a preorder and (b) mutual reachability as an equivalence
relation. Both come from the standard
`Relation.ReflTransGen` of Mathlib applied to the edge predicate;
this module just packages them under names that read naturally on
graphs.

Conceptual dependencies.
* `Reticulate.DirectedGraph` for the underlying graph record.
* Mathlib's `Relation.ReflTransGen` for reflexive-transitive closure.

Downstream consumers.
* `Reticulate.SCC` uses `MutuallyReachable` as the setoid that
  defines the SCC quotient.
* `Reticulate.Spec.Reachability` and `Reticulate.Spec.StateSpaceLattice`
  reason about reachability directly at the session-type level.
-/

namespace Reticulate

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `Reachable G u v` means: starting from vertex `u` you can follow
some sequence of edges in `G` (possibly zero edges) and arrive at
`v`. Formally it is the reflexive-transitive closure of
`G.edge`.

This is the fundamental "can-reach" relation we use throughout.
For session-type state spaces it captures "executing some prefix of
the protocol from state `u` eventually puts you in state `v`."

Consumed by every `Reachable.*` and `MutuallyReachable.*` lemma in
this module, by `SCCQuotient.le'` (the order on SCCs lifts pointwise
reachability), and by all `Reticulate.Spec.Reachability` lemmas. -/
def Reachable (G : FinDiGraph V) (u v : V) : Prop :=
  Relation.ReflTransGen G.edge u v

/-- Reachability is reflexive: every vertex reaches itself by the
empty path. Used as the base case in induction over reachability,
and to give `[v] ≤ [v]` on the SCC quotient. -/
theorem Reachable.refl (G : FinDiGraph V) (u : V) : Reachable G u u :=
  Relation.ReflTransGen.refl

/-- Reachability is transitive: if `u` reaches `v` and `v` reaches
`w` then `u` reaches `w`, simply by concatenating the two paths.
Used to lift a sequence of edge transitions into a single
reachability statement and to give transitivity on the SCC
quotient. -/
theorem Reachable.trans (G : FinDiGraph V) {u v w : V}
    (huv : Reachable G u v) (hvw : Reachable G v w) : Reachable G u w :=
  Relation.ReflTransGen.trans huv hvw

/-- Promote a single edge to a (length-one) reachability fact. The
inverse of "the edge `u -> v` is reachable in one step." Used
pervasively when lemmas about the state space need to lift an emitted
edge into a reachability statement. -/
theorem Reachable.single (G : FinDiGraph V) {u v : V}
    (h : G.edge u v) : Reachable G u v :=
  Relation.ReflTransGen.single h

/-- `MutuallyReachable G u v` means both `u` reaches `v` and `v`
reaches `u`. Two vertices satisfy this iff they belong to the same
strongly-connected component (SCC) of `G`.

For session-type state spaces, mutually reachable states represent
"the protocol can cycle back and forth between these positions";
in the SCC quotient they collapse to one element, which is what
makes the quotient a partial order rather than just a preorder. -/
def MutuallyReachable (G : FinDiGraph V) (u v : V) : Prop :=
  Reachable G u v ∧ Reachable G v u

/-- Mutual reachability is reflexive: every vertex is in its own SCC.
Used when the SCC equivalence relation needs a reflexivity proof. -/
theorem MutuallyReachable.refl (G : FinDiGraph V) (u : V) :
    MutuallyReachable G u u :=
  ⟨Reachable.refl G u, Reachable.refl G u⟩

/-- Mutual reachability is symmetric. Trivial: just swap the two
component reachability proofs. -/
theorem MutuallyReachable.symm (G : FinDiGraph V) {u v : V}
    (h : MutuallyReachable G u v) : MutuallyReachable G v u :=
  ⟨h.2, h.1⟩

/-- Mutual reachability is transitive. The forward direction
chains the two forward reachabilities; the backward direction
chains the two backward reachabilities (in reversed order). -/
theorem MutuallyReachable.trans (G : FinDiGraph V) {u v w : V}
    (huv : MutuallyReachable G u v) (hvw : MutuallyReachable G v w) :
    MutuallyReachable G u w :=
  ⟨(Reachable.trans G huv.1 hvw.1), (Reachable.trans G hvw.2 huv.2)⟩

/-- **Mutual reachability is an equivalence relation.**

This is the prerequisite for taking the SCC quotient: an equivalence
relation is exactly what `Setoid` needs as `iseqv`. Without this we
could not form the `Quotient (SCCSetoid G)` type used to define
`SCCQuotient` in `Reticulate.SCC`.

Proof: bundle `MutuallyReachable.refl`, `.symm`, and `.trans`. -/
theorem mutuallyReachable_equivalence (G : FinDiGraph V) :
    Equivalence (MutuallyReachable G) where
  refl := MutuallyReachable.refl G
  symm := MutuallyReachable.symm G
  trans := MutuallyReachable.trans G

end Reticulate
