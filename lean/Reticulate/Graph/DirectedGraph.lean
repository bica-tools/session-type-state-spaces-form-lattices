/-
Copyright (c) 2026 Alexandre Zua Caldeira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexandre Zua Caldeira
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic

/-!
# Finite directed graphs

This module gives the smallest possible record we need to talk about a
finite directed graph: a finite vertex set together with a decidable
"is there an edge from `u` to `v`?" predicate. It is the bottom layer
of the graph stack used to model session-type state spaces.

Why this matters for the project. Every session type `S` will be
turned into a directed graph (its **state space**). The lattice that
the paper studies — `\mathcal{L}(S)/\equiv` from §2 of the ICE 2026
paper — sits on top of *that* graph, after taking the SCC quotient.
We need a structure that is finite (so reachability is decidable)
and concrete (so we can compute on it inside Lean).

What this module exports.
* `Reticulate.FinDiGraph V` — a directed graph on the finite vertex
  type `V`, given by a decidable edge relation.

Conceptual dependencies.
* Mathlib's `Fintype` and `DecidableEq` typeclasses for finiteness
  and computable equality.

Downstream consumers.
* `Reticulate.Reachability` builds reflexive-transitive closure on
  these graphs.
* `Reticulate.SCC` quotients them by mutual reachability.
* `Reticulate.Spec.StateSpace` instantiates `FinDiGraph` for each
  session type `S` to produce its state space.
-/

namespace Reticulate

/-- A finite directed graph. The carrier is a finite type `V`; the
graph is described by an edge predicate `edge u v` together with a
proof that this predicate is decidable on every pair.

We deliberately keep the structure minimal: there are no edge labels,
no multi-edges, no source-target distinction beyond the predicate
itself. Session-type state spaces sometimes carry method or label
information at the edge level, but that information is irrelevant to
the lattice structure we eventually want to extract — only
reachability matters — so we drop it from the abstract model.

Used by every downstream module that needs to talk about state-space
reachability, in particular `Reachable`, `MutuallyReachable`,
`SCCQuotient`, and `Reticulate.Spec.SessionType.stateSpace`. -/
structure FinDiGraph (V : Type*) [Fintype V] [DecidableEq V] where
  /-- The edge predicate: `edge u v` holds when there is a directed
  edge from vertex `u` to vertex `v`. -/
  edge : V → V → Prop
  /-- Decidability witness: we can computationally test whether
  `edge u v` holds. This lets the typeclass machinery synthesise
  decidable `Reachable` and `MutuallyReachable` further down the
  stack. -/
  edge_decidable : DecidableRel edge

attribute [instance] FinDiGraph.edge_decidable

end Reticulate
