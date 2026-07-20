/-
Copyright (c) 2026 Alexandre Zua Caldeira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexandre Zua Caldeira
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Reticulate.Graph.DirectedGraph
import Reticulate.Spec.Core.SessionType

/-!
# State-space construction for session types

Given a session type `S`, build a finite directed graph whose
vertices are the "states" the protocol can be in and whose edges
are the one-step transitions. This is the construction the paper
calls `\mathcal{L}(S)` (`def:statespace` and the construction in
`def:construction` of §3) — before SCC quotienting. The lattice
machinery later sits on top of the SCC quotient of this graph.

What is exported.
* `stateCount S` — the number of states allocated for `S`. A
  structural recursion that gives an *upper bound* on the
  reachable states; some allocated states may turn out to be
  unreachable and are simply not connected by the edge relation.
* `State S := Fin (stateCount S)` — the carrier type.
* `edgeList S start env` — the list of `(source, target)` edges
  produced for `S` starting at offset `start` in the global index
  space, with environment `env` mapping bound recursion-variable
  names to their binder slots.
* `stateSpace S : FinDiGraph (State S)` — the assembled graph,
  using list membership as the decidable edge relation.
* `initialState S`, `terminalState S` — the canonical entry and
  exit states. Index `0` is always the entry.
* `exitSlot S start` — the absolute index where the subtree
  rooted at `S` (laid out at offset `start`) syntactically
  terminates.

Layout conventions, by constructor.
* `end_` allocates one state. No edges.
* `branch ms` allocates `2 + Σ stateCount sᵢ` states: a root, a
  local "bottom" terminator, and each child's subgraph.
* `select ls` is laid out identically (the polarity is irrelevant
  to the underlying graph).
* `par ss` allocates the n-ary product `Π stateCount sᵢ`,
  encoded row-major with the first child as the most significant
  coordinate. Edges are componentwise: lifting a child edge `(u,v)`
  emits product edges at every fixing of the other coordinates.
* `rec_ X body` reuses `body`'s layout; the binder name `X` is
  pushed onto `env` so any inner `var X` is routed back to the
  binder's slot.
* `var X` allocates one placeholder state and emits a single edge
  to whatever `env` maps `X` to.

Why this matters. Every lattice statement in
`Reticulate.Spec.StateSpaceLattice`, `Reticulate.Spec.Reachability`,
`Reticulate.Spec.Duality`, and `Reticulate.Spec.SubtypingEmbedding`
operates on the graph defined here. Concretely, the headline
`thm:reticulate` asserts that `SCCQuotient (stateSpace S)` is a
bounded lattice for every well-formed `S`.

Conceptual dependencies.
* `Reticulate.DirectedGraph` for the `FinDiGraph` record.
* `Reticulate.Spec.SessionType` for the AST.

Correspondence with the Python reference. This file is a
structurally-recursive port of `reticulate/reticulate/statespace.py`'s
`_Builder._build` algorithm. The Python version allocates fresh
state IDs on the fly; we pre-compute a state budget (`stateCount`)
so the carrier `Fin (stateCount S)` exists *before* the edge
relation, then define edges by structural recursion.

## Design choices

### `stateCount` as an upper bound

We follow the budget the phase brief prescribes:

* `end_` → `1` (single state, acts as the session terminator for that position).
* `branch ms` → `2 + Σ stateCount sᵢ` (one for the root, one for the branch's
  bottom, plus each child's subgraph budget).
* `select ls` → `2 + Σ stateCount sᵢ` (same shape as `branch`, distinguished by
  semantics of the edges — selection vs external choice).
* `par ss` → `Π stateCount sᵢ` (product carrier; the empty product is `1`).
* `rec_ X body` → `stateCount body` (unfold once; back-edges at the edge
  level via `env`).
* `var X` → `1` (placeholder; routed back to the binder's state by the edge
  relation, not by state identification).

This differs slightly from Python's on-the-fly allocation (which shares a
*global* `end_id`): we over-allocate a local "bottom" per `branch`/`select`.
Any unreachable states are simply not reached by the edge relation; the
`stateCount` is an upper bound, not a minimal count. 1b-β will prove
properties of the resulting graph; the upper-bound convention keeps the
structural-recursion equations clean.

### `stateSpace` as a list-of-edges decidable relation

`stateSpace S` is a `FinDiGraph (Fin (stateCount S))`. We build the edge set
as a `List (Nat × Nat)` and expose the edge relation as list membership;
`DecidableRel` then follows from `List.Mem` being decidable on `Nat × Nat`.

### Back-edges via environment, not merging

For `rec_ X body`, the Python builder allocates a placeholder state and then
*merges* it into the body's entry. In Lean we cannot merge `Fin` elements at
will; instead we keep the placeholder position distinct and route every
`var X` occurrence to the placeholder's index via a `List (String × Nat)`
environment threaded through the builder. A `var X` subterm emits a single
edge from its own slot to the placeholder's slot — no state identification
happens.

## Not in this phase

This file ships only definitions and `#eval` sanity checks. Lattice
instances, bounded-order structure, and the universal reticulate theorem
are deferred to 1b-β.
-/

namespace Reticulate.Spec

namespace SessionType

/-!
## State count

A structural recursion on `SessionType` that returns the size of the state
space budget. Inner `where` helpers traverse the list-shaped children.
-/

/-- Number of states allocated for the state space of `S`.

Structural recursion on the AST. Each constructor's contribution is
the layout budget described in the module-level header:

* `end_`, `var _` — `1` state (a single position).
* `branch ms`, `select ls` — `2 + Σᵢ stateCount sᵢ`: one for the
  root, one for the local "bottom", plus each child's subgraph.
* `par ss` — the product `Πᵢ stateCount sᵢ` (and `1` if `ss = []`).
* `rec_ _ body` — same as `body` (the binder reuses the body's
  layout).

Note: this is an *upper bound*, not an exact reachable-state count.
Some allocated states (such as a `branch`'s local "bottom" when the
children already glue back at their own bottoms) may be unreachable
in the resulting graph; they simply remain isolated.

Used pervasively to define `State S`, to bound endpoints in
`edgeList`, and to phrase reachability lemmas in
`Reticulate.Spec.Reachability`. -/
def stateCount : SessionType → Nat
  | .end_        => 1
  | .var _       => 1
  | .branch ms   => 2 + sumChildrenPair ms
  | .select ls   => 2 + sumChildrenPair ls
  | .par ss      => prodChildren ss
  | .rec_ _ body => stateCount body
where
  sumChildrenPair : List (String × SessionType) → Nat
    | []      => 0
    | p :: tl => stateCount p.2 + sumChildrenPair tl
  prodChildren : List SessionType → Nat
    | []      => 1
    | s :: tl => stateCount s * prodChildren tl

/-!
## Positivity of `stateCount`

Every session type has at least one state. Used to build `initialState`.
We prove positivity *before* defining `State`, since the `Inhabited`
instance depends on it.
-/

/-- Helper for `stateCount_pos`: the children product
`prodChildren xs` is positive whenever every element of `xs` has a
positive state count. Proof technique: induction on `xs`; empty
case is `1 > 0`, cons case uses `Nat.mul_pos` on the IH. -/
theorem stateCount.prodChildren_pos :
    ∀ (xs : List SessionType),
      (∀ s ∈ xs, 0 < stateCount s) → 0 < stateCount.prodChildren xs
  | [],      _ => by
      show 0 < 1
      decide
  | s :: tl, h => by
      have hs : 0 < stateCount s := h s (by simp)
      have htl : 0 < stateCount.prodChildren tl :=
        stateCount.prodChildren_pos tl (fun t ht => h t (by simp [ht]))
      show 0 < stateCount s * stateCount.prodChildren tl
      exact Nat.mul_pos hs htl

/-- Every session type has at least one state.

Needed before defining `State S` because the `Inhabited (State S)`
instance picks index `0`, which only exists when `stateCount S > 0`.
Proof technique: structural induction on `S`. The interesting case
is `par ss`, which delegates to `prodChildren_pos`. -/
theorem stateCount_pos : ∀ (S : SessionType), 0 < stateCount S
  | .end_        => Nat.succ_pos _
  | .var _       => Nat.succ_pos _
  | .branch ms   => by
      show 0 < 2 + stateCount.sumChildrenPair ms
      omega
  | .select ls   => by
      show 0 < 2 + stateCount.sumChildrenPair ls
      omega
  | .par ss      => by
      show 0 < stateCount.prodChildren ss
      exact stateCount.prodChildren_pos ss (fun s _ => stateCount_pos s)
  | .rec_ _ body => by
      show 0 < stateCount body
      exact stateCount_pos body

/-- The carrier type of states for the session type `S`.

A position in `S`'s state space is encoded as a natural number less
than `stateCount S`. We use `Fin` so finiteness, decidable
equality, and inhabitedness all come automatically.

Used as the vertex type of `stateSpace S`, and pervasively in
reachability and lattice statements. -/
def State (S : SessionType) : Type := Fin (stateCount S)

namespace State

instance (S : SessionType) : Fintype (State S) := by
  unfold State
  exact inferInstance

instance (S : SessionType) : DecidableEq (State S) := by
  unfold State
  exact inferInstance

instance (S : SessionType) : Inhabited (State S) :=
  ⟨⟨0, stateCount_pos S⟩⟩

end State

/-!
## Edge list construction

We compute a `List (Nat × Nat)` of edges structurally. The builder is
parameterised by:

* `start : Nat` — the offset at which this subtree's states begin in the
  global `Fin (stateCount top)` index space.
* `env : List (String × Nat)` — maps bound `var X` names to the absolute
  index of the enclosing `rec_ X` binder's slot. When a `var X` subterm is
  encountered, we emit an edge from its own slot to `env.lookup X`.
* `parentBottom : Nat` — the slot at which the enclosing `branch` / `select`
  expects children to glue back. For the top-level call, this is an
  arbitrary sentinel; internal states that have no glue-back semantics
  simply do not emit glue edges.

### Layout per constructor

For a `branch ms` (or `select ls`) laid out at offset `start` with total
size `2 + Σ stateCount sᵢ`:

* `start` = root (entry of the branch node)
* `start + 1` = bottom (local terminator for this branch node)
* `start + 2 ..` = child subgraphs, concatenated in order.

For each child `(mᵢ, sᵢ)` placed at `childStart = start + 2 + Σ prior`:
* emit edge `(start, childStart)` — entry → child's entry.
* recursively build `sᵢ` at offset `childStart`, passing `parentBottom = start + 1`.
* emit `(childExit, start + 1)` — child's "exit" slot → parent's bottom.
  The exit slot depends on the child's top-level constructor and is the
  slot at which the child's "body has terminated" — for `end_`, the child
  itself; for another `branch` / `select`, its own bottom; etc.

For `par ss`, the layout is the N-ary Cartesian product of the children's
state spaces. Edges are "move one component" transitions.

For `rec_ X body`, layout = `body`; `env` gets `X ↦ start` pushed.

For `var X`, layout = one state; emit edge `(start, env.lookup X)`.

For `end_`, layout = one state; no edges.

### Concrete exit-slot convention

We define `exitSlot S start` = the absolute index at which a subtree
terminates:

* `end_` at `start` — exit is `start` (itself).
* `var X` at `start` — exit is `start` (the placeholder; no "natural" exit).
* `branch ms` at `start` — exit is `start + 1` (its local bottom).
* `select ls` at `start` — exit is `start + 1` (its local bottom).
* `par ss` at `start` — exit is the last state of the product (bottom-right
  corner), which is `start + stateCount (par ss) - 1` by construction.
* `rec_ X body` at `start` — exit is `exitSlot body start`.
-/

/-!
`exitSlot` is defined mutually with `parExitFlat`:

* For `.par ss`, the semantic exit is the tuple `(⊥₁, ⊥₂, …, ⊥ₙ)` of child
  bottoms, encoded row-major via `parExitFlat`. The earlier formula
  `start + prodChildren ss - 1` only coincides with the semantic exit when
  every child's local exit-slot is `stateCount sᵢ - 1`, which is false
  whenever a child is a `branch`/`select`/`rec_` with sub-structure above
  its bottom. See `papers/publications/ice-2026/audit-findings.md` (finding 3).

* `parExitFlat [s₁, …, sₙ] = exitSlot s₁ 0 · (s₂·…·sₙ) + … + exitSlot sₙ 0`.
  The first child is most significant, matching the layout used by
  `edgeListParGo` (walk children left-to-right, `prefixProd` = left stride).
-/
mutual

/-- The absolute index where the subtree rooted at `S`, laid out at
offset `start`, syntactically terminates.

For each constructor:
* `end_` and `var _` — exit at `start` itself (a single state).
* `branch _` and `select _` — exit at `start + 1` (the local
  "bottom" slot, slot 1 of the layout).
* `par ss` — exit at `start + parExitFlat ss`, the row-major
  encoding of the tuple `(⊥₁, …, ⊥ₙ)` of child exit slots.
* `rec_ _ body` — same as the body's exit (the binder reuses
  layout).

This is the slot at which a `branch`/`select` parent expects its
child to glue back. Used pervasively in `edgeList` (the
`exitEdge` of every child) and in
`Reticulate.Spec.Reachability` to prove "every state reaches the
exit." -/
def exitSlot : SessionType → Nat → Nat
  | .end_,        start => start
  | .var _,       start => start
  | .branch _,    start => start + 1
  | .select _,    start => start + 1
  | .par ss,      start => start + parExitFlat ss
  | .rec_ _ body, start => exitSlot body start

/-- Row-major flat encoding of the tuple of child exit-slots for
`par`'s child list `ss`.

If `ss = [s₁, …, sₙ]` and child `i` has exit slot `eᵢ` (relative
to its own start), this is `e₁·(s₂·…·sₙ) + e₂·(s₃·…·sₙ) + … + eₙ`,
viewing `s₁` as the most significant coordinate of the product
encoding. The empty list returns `0` (vacuous product index).

Required for `exitSlot` on `par`. The earlier convention of using
`stateCount (par ss) - 1` as the par exit was wrong for children
with internal branching (Audit Finding 3); this row-major encoding
is the correct semantic exit. -/
def parExitFlat : List SessionType → Nat
  | []      => 0
  | s :: tl => exitSlot s 0 * stateCount.prodChildren tl + parExitFlat tl

end

/-!
### Edge list builder

We emit edges as `List (Nat × Nat)`. The absolute indexing lets us inherit
into the final `Fin (stateCount S)` space at the top-level call by
discarding any out-of-range edges (there should be none for well-layouted
builds, but we clip defensively in the relation).
-/

/-- Look up a recursion-variable name in the environment.

The environment threaded through `edgeList` maps each in-scope
binder name `X` to the absolute index of its `rec_ X` slot.
`envLookup` is straight `lookup`-by-key on the assoc-list; it
returns `none` only when the name is free, in which case
`edgeList` emits no edge for that occurrence (the type is then
`closed`-rejected upstream). -/
def envLookup : List (String × Nat) → String → Option Nat
  | [],            _ => none
  | (y, n) :: tl,  x => if y = x then some n else envLookup tl x

/-- The edge-list builder.

Computes the list of `(source, target)` edges for the subtree `S`
laid out at offset `start`, with environment `env` mapping in-scope
recursion-variable names to their binder slots.

The builder is structurally recursive on `S`. Inner `where`
clauses traverse the list-shaped children:

* `edgeListBranchChildren` lays out `branch`/`select` children
  in sequence, emitting `entryEdge = (root, childStart)` and
  `exitEdge = (child.exit, bottom)` plus the child's internal
  edges.
* `edgeListPar` enters the `par` case via `edgeListParGo`,
  walking children left-to-right and lifting each child's local
  edges across the product index space (see the docstring there
  for the row-major encoding).

Constructor cases at a glance:
* `end_` — no edges.
* `var X` — emits `(start, env.lookup X)` if `X` is bound;
  nothing otherwise (free variables are caught by `closed`).
* `branch ms` — for non-empty `ms`, the children's
  entry/exit/internal edges. For empty `ms` (the `&{}` boundary
  case), prepend a single `(root, bottom)` edge so the resulting
  graph is still the 2-element lattice; without this prefix the
  empty branch would produce an edge-less graph.
* `select ls` — symmetric to `branch`.
* `par ss` — delegates to `edgeListPar`, which encodes
  componentwise transitions in the product index space.
* `rec_ X body` — recurses into `body` with `(X, start)` pushed
  onto `env`; the binder allocates no extra state.

The built list of edges is consumed by `stateSpace S` below, which
exposes list membership as the (decidable) edge predicate. -/
def edgeList : SessionType → Nat → List (String × Nat) → List (Nat × Nat)
  | .end_,         _,     _   => []
  | .var X,        start, env =>
      match envLookup env X with
      | some target => [(start, target)]
      | none        => []   -- free `var X`: no edge emitted
  | .branch ms,    start, env =>
      -- root = start, bottom = start + 1
      -- Approach (2): special-case the empty branch `&{}` so that the
      -- 2-element lattice `{q₀, q_⊥}` has its `q₀ ≤ q_⊥` edge. For
      -- non-empty children, the root→bottom reachability already holds
      -- via the children's entry/exit edges, so we omit the direct edge
      -- to keep existing edge counts unchanged. See the ICE 2026
      -- Phase 1b-β1a note on n=0 branch/select duality.
      --
      -- Implemented as a prefix `emptyEdges` (the extra root→bottom pair
      -- when `ms = []`) plus the existing `edgeListBranchChildren` call,
      -- rather than an outer `match ms with`, so that Lean's structural
      -- recursion on `SessionType` (via the `edgeListBranchChildren`
      -- helper) remains visible — an outer `match` blocks inference.
      let root := start
      let bottom := start + 1
      let emptyEdges : List (Nat × Nat) :=
        if ms.isEmpty then [(root, bottom)] else []
      emptyEdges ++ edgeListBranchChildren ms (start + 2) root bottom env
  | .select ls,    start, env =>
      -- Symmetric to `.branch`, Approach (2): empty selection `+{}`
      -- emits the single `q₀ → q_⊥` edge so its state space is the
      -- 2-element lattice; non-empty selections are unchanged.
      let root := start
      let bottom := start + 1
      let emptyEdges : List (Nat × Nat) :=
        if ls.isEmpty then [(root, bottom)] else []
      emptyEdges ++ edgeListBranchChildren ls (start + 2) root bottom env
  | .par ss,       start, env =>
      edgeListPar ss start env
  | .rec_ X body,  start, env =>
      -- Push X ↦ start (the placeholder's absolute index equals body's start
      -- because rec_ doesn't allocate its own state in `stateCount`).
      edgeList body start ((X, start) :: env)
where
  /-- Layout successive children of a branch/select, emitting root→child
      and child.exit→bottom edges plus internal child edges. -/
  edgeListBranchChildren :
      List (String × SessionType) → Nat → Nat → Nat → List (String × Nat) →
      List (Nat × Nat)
    | [],           _,          _,    _,      _   => []
    | (_, s) :: tl, childStart, root, bottom, env =>
        let childEdges := edgeList s childStart env
        let entryEdge : Nat × Nat := (root, childStart)
        let exitEdge : Nat × Nat := (exitSlot s childStart, bottom)
        let childSize := stateCount s
        let restEdges :=
          edgeListBranchChildren tl (childStart + childSize) root bottom env
        entryEdge :: exitEdge :: childEdges ++ restEdges
  /-- For `par`, emit the "move one component" n-ary product edges.

      Layout: `stateCount (par ss) = Πᵢ stateCount sᵢ = prodChildren ss`,
      with the recursion `stateCount s_head * prodChildren tl`. This is a
      row-major / "first component most significant" encoding: a flat index
      `k ∈ [0, Π stateCount sᵢ)` decodes as
        `q₁ = k / (s₂ * s₃ * … * sₙ)`
        `q₂ = (k mod (s₂ * … * sₙ)) / (s₃ * … * sₙ)`
        …
        `qₙ = k mod sₙ`.
      Equivalently:
        `k = q₁ · (s₂·…·sₙ) + q₂ · (s₃·…·sₙ) + … + qₙ`.

      For each child `i`, an edge `(u, u')` of `stateSpace sᵢ` lifts to
      product edges at every combination of the *other* coordinates. The
      stride of coordinate `i` is `suffixProd i = Πⱼ>ᵢ stateCount sⱼ`, so
      replacing `qᵢ = u` with `qᵢ' = u'` at base index
        `base = p · (sᵢ · suffixProd) + q`
      (where `p ∈ [0, prefixProd)` iterates the first i−1 coordinates'
      combined index and `q ∈ [0, suffixProd)` iterates the last n−i
      coordinates) gives the pair
        (start + base + u · suffixProd, start + base + u' · suffixProd).

      Implementation (Option B — suffix-product strides): we walk `ss`
      left-to-right, maintaining `prefixProd` (states already consumed).
      For the current child we compute its local edges via
      `edgeList child 0 env`, filter those whose endpoints are in-range
      (drops any outgoing `var X` edges whose `env` target lies outside
      the child's local range — those are handled at the par-external
      level by construction), and expand each such edge across the
      prefix × suffix combinations. -/
  edgeListPar : List SessionType → Nat → List (String × Nat) → List (Nat × Nat)
    | ss, start, env =>
        edgeListParGo ss start env 1
  /-- Walk the children left-to-right, carrying `prefixProd` (product of
      sizes already seen to the left). `start` points at the par's base
      offset in the global index space. -/
  edgeListParGo :
      List SessionType → Nat → List (String × Nat) → Nat →
      List (Nat × Nat)
    | [],       _,     _,   _         => []
    | s :: tl,  start, env, prefixProd =>
        let size := stateCount s
        let suffixProd := stateCount.prodChildren tl
        -- child's local edges (in [0, size)-space for regular edges;
        -- free `var` or cross-region edges are filtered below)
        let rawChild := edgeList s 0 env
        let localEdges :=
          rawChild.filter (fun e => decide (e.1 < size) && decide (e.2 < size))
        let liftedForThis :=
          edgeListParLiftChild localEdges start suffixProd size prefixProd
        let restEdges :=
          edgeListParGo tl start env (prefixProd * size)
        liftedForThis ++ restEdges
  /-- For a fixed child with local edges `edges`, lift each `(u, u')` edge
      across every `(p, q)` ∈ [0, prefixProd) × [0, suffixProd). -/
  edgeListParLiftChild :
      List (Nat × Nat) → Nat → Nat → Nat → Nat →
      List (Nat × Nat)
    | [],            _,     _,          _,    _          => []
    | (u, v) :: tl,  start, suffixProd, size, prefixProd =>
        let here := edgeListParLiftOne u v start suffixProd size prefixProd 0
        let rest := edgeListParLiftChild tl start suffixProd size prefixProd
        here ++ rest
  /-- Lift a single `(u, v)` child-edge across all `p ∈ [0, prefixProd)`,
      iterating `p` from `p` up to `prefixProd - 1`. Inner loop over `q`
      is delegated to `edgeListParLiftSuffix`. -/
  edgeListParLiftOne :
      Nat → Nat → Nat → Nat → Nat → Nat → Nat →
      List (Nat × Nat)
    | u, v, start, suffixProd, size, prefixProd, p =>
        if _h : p < prefixProd then
          let pBase := p * (size * suffixProd)
          let here :=
            edgeListParLiftSuffix u v start suffixProd size pBase 0
          let rest :=
            edgeListParLiftOne u v start suffixProd size prefixProd (p + 1)
          here ++ rest
        else []
  termination_by _ _ _ _ _ prefixProd p => prefixProd - p
  decreasing_by all_goals omega
  /-- For a fixed `(u, v)` child-edge and a fixed prefix base `pBase`,
      iterate `q ∈ [0, suffixProd)` emitting the pair
        (start + pBase + u * suffixProd + q,
         start + pBase + v * suffixProd + q). -/
  edgeListParLiftSuffix :
      Nat → Nat → Nat → Nat → Nat → Nat → Nat →
      List (Nat × Nat)
    | u, v, start, suffixProd, size, pBase, q =>
        if _h : q < suffixProd then
          let src := start + pBase + u * suffixProd + q
          let tgt := start + pBase + v * suffixProd + q
          (src, tgt) ::
            edgeListParLiftSuffix u v start suffixProd size pBase (q + 1)
        else []
  termination_by _ _ _ suffixProd _ _ q => suffixProd - q
  decreasing_by all_goals omega

/-!
## `stateSpace` — the `FinDiGraph`

We lift `edgeList` to the carrier type `State S` by taking edges `(u, v)`
with `u < stateCount S` and `v < stateCount S`, and using list membership
as the (decidable) edge predicate.
-/

/-- The state-space graph of `S`: the `FinDiGraph` whose vertices
are `State S` and whose edges are list-membership in
`edgeList S 0 []`.

This is the construction the paper denotes `\mathcal{L}(S)` (see
`def:statespace`, `def:construction`, `def:product-construction`).
Every theorem about lattices on session-type state spaces — from
the unconditional `instBoundedOrder` to `thm:reticulate` — speaks
about this graph (or its SCC quotient). -/
def stateSpace (S : SessionType) : Reticulate.FinDiGraph (State S) where
  edge u v := (u.val, v.val) ∈ edgeList S 0 []
  edge_decidable := fun u v =>
    inferInstanceAs (Decidable ((u.val, v.val) ∈ edgeList S 0 []))

/-!
## Initial and terminal states

The **initial state** is always index `0` — by construction, the root of the
top-level construct sits at offset `0`. The **terminal states** are those
that correspond to `end_`-like positions:

* for `end_` itself, the single state;
* for `branch` / `select`, the local bottom at offset `1` (the exit slot);
* for `par`, the product bottom at the last index.

For Phase 1b-α we expose a conservative approximation: the top-level exit
slot. 1b-β may refine this to a `Finset` that collects all `end_` positions.
-/

/-- The designated initial state of `S`'s state space: index `0`.

By the layout convention, the root of the top-level constructor
sits at offset `0`, so `initialState S = ⟨0, _⟩`. After SCC
quotienting this becomes the lattice's `⊥`. Used to define
`BoundedOrder` on the SCC quotient and as the universal source in
`rootReachesAll`. -/
def initialState (S : SessionType) : State S :=
  ⟨0, stateCount_pos S⟩

/-- The designated terminal (top-level exit) state of `S`'s state
space: `exitSlot S 0`, with a fallback to `initialState` when the
exit slot is out of range.

The fallback is defensive only — `exitSlot_lt` proves
`exitSlot S 0 < stateCount S` for every `S`, so the `else` branch
is unreachable in practice. We keep it to make the definition total
without a side condition. After SCC quotienting,
`[terminalState S]` becomes the lattice's `⊤`. Used in
`instBoundedOrder` and in `allReachExit`. -/
def terminalState (S : SessionType) : State S :=
  let e := exitSlot S 0
  if h : e < stateCount S then ⟨e, h⟩ else initialState S

/-- A conservative terminal-state set: the singleton `{terminalState S}`.

Phase-1b-α convention: at the moment we identify a single
top-level exit. Future phases may extend this to the full set of
indices that correspond to `end_` positions inside the AST. -/
def terminalStates (S : SessionType) : Finset (State S) :=
  {terminalState S}

/-!
## `#eval` sanity checks

Verify that `stateCount` computes deterministically on small cases.
-/

-- `end_`: single state.
#eval stateCount (.end_ : SessionType)

-- Simple branch: 2 (root + bottom) + 1 (end child) = 3.
#eval stateCount (.branch [("a", .end_)] : SessionType)

-- Empty branch `&{}` — the n = 0 boundary: 2 + 0 = 2.
#eval stateCount (.branch [] : SessionType)

-- Empty selection `+{}` — same shape: 2.
#eval stateCount (.select [] : SessionType)

-- Nested: `&{a: end, b: end}`: 2 + (1 + 1) = 4.
#eval stateCount (.branch [("a", .end_), ("b", .end_)] : SessionType)

-- Recursion guarded by a branch: `rec X . &{a:X, done:end}`.
-- body = branch = 2 + (1 + 1) = 4; rec_ = body = 4.
#eval stateCount (.rec_ "X" (.branch [("a", .var "X"), ("done", .end_)]) : SessionType)

-- A47h well-formed witness:
-- `par [rec X . &{a:X, done:end}, &{b:end}]`
-- = prod(4, 3) = 12.
#eval stateCount
  (.par [.rec_ "X" (.branch [("a", .var "X"), ("done", .end_)]),
         .branch [("b", .end_)]] : SessionType)

-- Counterexample ill-formed witness:
-- `&{a:end, b:rec X . &{a:X}}`
-- inner body = &{a:X} = 2 + 1 = 3; rec = 3; outer = 2 + (1 + 3) = 6.
#eval stateCount
  (.branch [("a", .end_),
            ("b", .rec_ "X" (.branch [("a", .var "X")]))] : SessionType)

-- Parallel degenerate cases.
#eval stateCount (.par [] : SessionType)             -- empty product = 1.
#eval stateCount (.par [.end_] : SessionType)        -- 1.
#eval stateCount (.par [.end_, .end_] : SessionType) -- 1 * 1 = 1.

-- Single recursion variable under its binder.
#eval stateCount (.rec_ "X" (.var "X") : SessionType) -- stateCount (var X) = 1.

-- Smoke test for edge count on a trivial type.
#eval (edgeList (.end_ : SessionType) 0 []).length           -- expect 0
#eval (edgeList (.branch [("a", .end_)] : SessionType) 0 []).length
-- Expected: 2 edges — root→child (root→2) and child_exit→bottom (2→1).

-- Phase 1b-β1a smoke tests: empty branch/select now emit the q₀ → q_⊥ edge.
-- Before fix: both were 0 (bug). After fix: both are ≥ 1.
#eval (edgeList (.branch [] : SessionType) 0 []).length      -- expect ≥ 1
#eval (edgeList (.select [] : SessionType) 0 []).length      -- expect ≥ 1

/-!
## Phase 1b-α′ — `edgeListPar` sanity checks

We verify the n-ary product edge allocator on three witnesses:
* `par [end, end]` — every child has one state and zero edges, so the
  product has one state and zero edges.
* `par [&{a:end}, &{b:end}]` — each child has `stateCount = 3` and two
  edges (root→child, child_exit→bottom). The product has `3 * 3 = 9`
  states and `2 * 3 + 3 * 2 = 12` componentwise edges.
* A47h witness `par [rec X . &{a:X, done:end}, &{b:end}]` — the left
  child has 4 states and 5 edges (root→a-child, a-exit→bottom,
  root→done-child, done-exit→bottom, plus the `var X` back-edge to the
  rec binder at slot 0 which is in range), the right child has 3 states
  and 2 edges. Lifting: `5 * 3 + 4 * 2 = 23` product edges.
-/

-- Simplest par: end || end = 1 * 1 = 1 state, 0 edges.
#eval (edgeList.edgeListPar [.end_, .end_] 0 []).length      -- expect 0

-- par [&{a:end}, &{b:end}] — each child has 3 states, 3*3 = 9 product states.
#eval stateCount
  (.par [.branch [("a", .end_)], .branch [("b", .end_)]] : SessionType)  -- expect 9
#eval (edgeList.edgeListPar
  [.branch [("a", .end_)], .branch [("b", .end_)]] 0 []).length
-- Expected: 2 (left edges) * 3 (right states) + 3 (left states) * 2 (right edges) = 12.

-- A47h well-formed witness.
#eval (edgeList.edgeListPar
  [.rec_ "X" (.branch [("a", .var "X"), ("done", .end_)]),
   .branch [("b", .end_)]] 0 []).length
-- Left child edge count times 3 (right states) plus 4 (left states) times 2 (right edges).

-- Component sanity: left child alone and right child alone.
#eval (edgeList
  (.rec_ "X" (.branch [("a", .var "X"), ("done", .end_)]) : SessionType) 0 []).length
  -- left child edges count
#eval (edgeList (.branch [("b", .end_)] : SessionType) 0 []).length
  -- right child edges count

end SessionType

end Reticulate.Spec
