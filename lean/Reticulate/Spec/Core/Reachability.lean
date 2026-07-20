/-
Copyright (c) 2026 Alexandre Zua Caldeira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexandre Zua Caldeira
-/

import Mathlib.Logic.Relation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Reticulate.Spec.StateSpace.StateSpace
import Reticulate.Spec.StateSpace.StateSpaceEdges

/-!
# Reachability lemmas on the state-space graph

This is the workhorse module that proves every state in
`stateSpace S` sits below the top SCC and above the bottom SCC.
Concretely it establishes two universal facts:

* **Top reaches everything** (`rootReachesAll_uncond`): for every
  session type `S`, the entry state at index `0` reaches every
  state of `stateSpace S`.
* **Everything reaches the bottom** (`allReachExit_uncond`): for
  every `S` and every state, there is a path to the exit slot
  `exitSlot S 0`.

Together with the SCC quotient from `Reticulate.SCC`, these give
the unconditional `BoundedOrder` instance on
`SCCQuotient (stateSpace S)` (proved in
`Reticulate.Spec.StateSpaceLattice.instBoundedOrder`). The
existence of `⊤` and `⊥` for the lattice argument of
`thm:reticulate` rests on exactly these two theorems. They also
underwrite `prop:extrema` of §3 of the paper (unique extrema in
the SCC quotient) by giving the universal reachability witnesses
that make the extrema unique up to `≈`.

What is exported.
* `edgeRel S start env` — abbreviation for
  `(u, v) ∈ edgeList S start env` viewed as a binary relation on
  `Nat`.
* `BothReach S env start` — the conjunction "root reaches
  everything within `S`'s allocated range" + "everything in the
  range reaches the exit slot."
* `stateSpace_connected_uncond` — `BothReach S [] 0` for every
  `S`. The unconditional form.
* `rootReachesAll_uncond` and `allReachExit_uncond` — the two
  conjuncts as standalone theorems.
* `branch_edge_taxonomy`, `select_edge_taxonomy` — every
  `branch`/`select` edge is one of three kinds: a `(root, child-entry)`
  entry edge, a `(child-exit, bottom)` exit edge, or an internal
  child edge. Used pervasively when reasoning about which edges
  enter/leave a child sub-region.
* Range and bottom-no-outgoing taxonomies for branch/select used by
  the lattice file.

Strategy. The two reachability statements are proved jointly by
structural induction on `SessionType`, packaged as a single
predicate `BothReach`. Inner helpers handle list-shaped branch and
select children. The `par` case routes through the row-major
product encoding and requires a separate stride-arithmetic
chain (Lemma B–C and the lift/unlift family); the inductive step
for `par` is isolated as `par_connected_from_children`, then
discharged unconditionally.

Conceptual dependencies.
* `Reticulate.Spec.StateSpace` for the builder, `stateCount`,
  `exitSlot`, `parExitFlat`.
* `Reticulate.Spec.StateSpaceEdges` for the `par`-helper
  membership rewrites.

Downstream consumers.
* `Reticulate.Spec.StateSpaceLattice` for the `BoundedOrder` and
  `Lattice` instances.
* `Reticulate.Spec.Duality` and `Reticulate.Spec.SubtypingEmbedding`
  rely on the reachability statements for the order-iso /
  embedding constructions.
-/

namespace Reticulate.Spec

namespace SessionType

open Relation (ReflTransGen)

/-!
## The edge relation used throughout this file

We work with the binary relation `edgeRel S start env u v := (u, v) ∈
edgeList S start env` and its reflexive-transitive closure.
-/

/-- The edge relation on `Nat`-typed indices derived from
`edgeList S start env`.

A binary predicate `edgeRel S start env u v` that holds iff the
pair `(u, v)` appears in the builder's emitted edge list. Working
at the `Nat` level (rather than `Fin`) lets us write shift and
range lemmas without constantly threading `Fin` bounds. The
`Fin`-level translation into `stateSpace S`-reachability happens
in `StateSpaceLattice.reachable_of_edgeRel`.

Used as the relation argument of `Relation.ReflTransGen`
throughout this module. -/
abbrev edgeRel (S : SessionType) (start : Nat) (env : List (String × Nat)) :
    Nat → Nat → Prop := fun u v => (u, v) ∈ edgeList S start env

/-!
## Edge inclusion lemmas for `branch`/`select`
-/

/-- Every edge emitted by `edgeList s childStart env` is also emitted by
`edgeListBranchChildren ((m, s) :: tl) childStart root bottom env`. -/
theorem edgeListBranchChildren_sub_first
    (m : String) (s : SessionType)
    (tl : List (String × SessionType))
    (childStart root bottom : Nat)
    (env : List (String × Nat))
    {u v : Nat}
    (h : (u, v) ∈ edgeList s childStart env) :
    (u, v) ∈ edgeList.edgeListBranchChildren ((m, s) :: tl) childStart
      root bottom env := by
  simp only [edgeList.edgeListBranchChildren]
  right; right
  exact List.mem_append.mpr (Or.inl h)

/-- Every edge emitted by
`edgeListBranchChildren tl (childStart + stateCount s) root bottom env`
is also emitted by
`edgeListBranchChildren ((m, s) :: tl) childStart root bottom env`. -/
theorem edgeListBranchChildren_sub_rest
    (m : String) (s : SessionType)
    (tl : List (String × SessionType))
    (childStart root bottom : Nat)
    (env : List (String × Nat))
    {u v : Nat}
    (h : (u, v) ∈ edgeList.edgeListBranchChildren tl
            (childStart + stateCount s) root bottom env) :
    (u, v) ∈ edgeList.edgeListBranchChildren ((m, s) :: tl) childStart
      root bottom env := by
  simp only [edgeList.edgeListBranchChildren]
  right; right
  exact List.mem_append.mpr (Or.inr h)

/-- Entry edge `(root, childStart)` is present in
`edgeListBranchChildren ((m, s) :: tl) childStart root bottom env`. -/
theorem edgeListBranchChildren_entry
    (m : String) (s : SessionType)
    (tl : List (String × SessionType))
    (childStart root bottom : Nat)
    (env : List (String × Nat)) :
    (root, childStart) ∈ edgeList.edgeListBranchChildren ((m, s) :: tl)
      childStart root bottom env := by
  simp [edgeList.edgeListBranchChildren]

/-- Exit edge `(exitSlot s childStart, bottom)` is present in
`edgeListBranchChildren ((m, s) :: tl) childStart root bottom env`. -/
theorem edgeListBranchChildren_exit
    (m : String) (s : SessionType)
    (tl : List (String × SessionType))
    (childStart root bottom : Nat)
    (env : List (String × Nat)) :
    (exitSlot s childStart, bottom) ∈
      edgeList.edgeListBranchChildren ((m, s) :: tl)
        childStart root bottom env := by
  simp [edgeList.edgeListBranchChildren]

/-- Edges of `edgeListBranchChildren` appear in `edgeList (.branch ms) start env`. -/
theorem edgeList_branch_of_children
    (ms : List (String × SessionType))
    (start : Nat) (env : List (String × Nat))
    {u v : Nat}
    (h : (u, v) ∈ edgeList.edgeListBranchChildren ms (start + 2)
            start (start + 1) env) :
    (u, v) ∈ edgeList (.branch ms) start env := by
  simp only [edgeList]
  exact List.mem_append.mpr (Or.inr h)

/-- Edges of `edgeListBranchChildren` appear in `edgeList (.select ls) start env`. -/
theorem edgeList_select_of_children
    (ls : List (String × SessionType))
    (start : Nat) (env : List (String × Nat))
    {u v : Nat}
    (h : (u, v) ∈ edgeList.edgeListBranchChildren ls (start + 2)
            start (start + 1) env) :
    (u, v) ∈ edgeList (.select ls) start env := by
  simp only [edgeList]
  exact List.mem_append.mpr (Or.inr h)

/-- For empty branch, the direct `(start, start + 1)` edge is present. -/
theorem edgeList_empty_branch
    (start : Nat) (env : List (String × Nat)) :
    (start, start + 1) ∈ edgeList (.branch [] : SessionType) start env := by
  simp [edgeList]

/-- For empty select, the direct `(start, start + 1)` edge is present. -/
theorem edgeList_empty_select
    (start : Nat) (env : List (String × Nat)) :
    (start, start + 1) ∈ edgeList (.select [] : SessionType) start env := by
  simp [edgeList]

/-!
## exitSlot within the allocated range
-/

/-- `start ≤ exitSlot S start`. -/
theorem start_le_exitSlot : ∀ (S : SessionType) (start : Nat),
    start ≤ exitSlot S start
  | .end_, start => by simp [exitSlot]
  | .var _, start => by simp [exitSlot]
  | .branch _, start => by
      simp only [exitSlot]
      omega
  | .select _, start => by
      simp only [exitSlot]
      omega
  | .par ss, start => by
      simp only [exitSlot]
      exact Nat.le_add_right _ _
  | .rec_ _ body, start => by
      simp only [exitSlot]
      exact start_le_exitSlot body start

/-!
### `exitSlot_lt` and `parExitFlat_lt`

For the par case, `exitSlot (.par ss) start = start + parExitFlat ss`, and
we need `parExitFlat ss < prodChildren ss`. These two bounds are mutually
recursive: `exitSlot_lt` on `.par ss` needs `parExitFlat_lt ss`, which
needs `exitSlot_lt` on each head at `start = 0`. We break the recursion
by joint induction on `sizeOf`.
-/

mutual

/-- `exitSlot S start < start + stateCount S`. -/
theorem exitSlot_lt : ∀ (S : SessionType) (start : Nat),
    exitSlot S start < start + stateCount S
  | .end_, start => by simp [exitSlot, stateCount]
  | .var _, start => by simp [exitSlot, stateCount]
  | .branch _, start => by
      simp only [exitSlot, stateCount]
      omega
  | .select _, start => by
      simp only [exitSlot, stateCount]
      omega
  | .par ss, start => by
      simp only [exitSlot, stateCount]
      have h := parExitFlat_lt ss
      omega
  | .rec_ _ body, start => by
      simp only [exitSlot, stateCount]
      exact exitSlot_lt body start

/-- `parExitFlat ss < prodChildren ss`: the flat-encoded child-exit tuple
always fits into the product index space. -/
theorem parExitFlat_lt : ∀ (ss : List SessionType),
    parExitFlat ss < stateCount.prodChildren ss
  | [] => by
      simp [parExitFlat, stateCount.prodChildren]
  | s :: tl => by
      -- parExitFlat (s :: tl) = exitSlot s 0 * prodChildren tl + parExitFlat tl
      -- Goal: < stateCount s * prodChildren tl
      have hs : exitSlot s 0 < stateCount s := by
        have := exitSlot_lt s 0; omega
      have htl : parExitFlat tl < stateCount.prodChildren tl := parExitFlat_lt tl
      -- exitSlot s 0 ≤ stateCount s - 1, so
      -- exitSlot s 0 * prodChildren tl + parExitFlat tl
      --   ≤ (stateCount s - 1) * prodChildren tl + (prodChildren tl - 1)
      --   = stateCount s * prodChildren tl - 1
      --   < stateCount s * prodChildren tl
      simp only [parExitFlat, stateCount.prodChildren]
      have hpc_pos : 0 < stateCount.prodChildren tl := by
        -- from parExitFlat_lt tl: parExitFlat tl < prodChildren tl; so prodChildren tl > parExitFlat tl ≥ 0
        omega
      calc exitSlot s 0 * stateCount.prodChildren tl + parExitFlat tl
          < exitSlot s 0 * stateCount.prodChildren tl + stateCount.prodChildren tl := by omega
        _ = (exitSlot s 0 + 1) * stateCount.prodChildren tl := by ring
        _ ≤ stateCount s * stateCount.prodChildren tl :=
            Nat.mul_le_mul_right _ hs

end

/-!
## Joint reachability theorem (everything except `par`)

We prove both `rootReachesAll` and `allReachExit` simultaneously via a
single structural recursion on `SessionType`.  The `par` case is isolated
behind a hypothesis `hPar` that will be discharged in Phase 1b-β1c.

Package:
* `Rroot S start env k` = reachability from `start` to `start + k`.
* `Rexit S start env k` = reachability from `start + k` to `exitSlot S start`.

We bundle both into a conjunction to share the structural-recursion
scaffold.
-/

/-- The "both-ways reachability" bundle: every state in `S`'s
allocated range is reachable from the root, and reaches the exit.

Concretely: `BothReach S env start` says that for every
`k < stateCount S`, the index `start + k` is both
* reachable from `start` (root) by the reflexive-transitive
  closure of the edge relation, and
* able to reach `exitSlot S start`.

We bundle the two so a single structural induction discharges both
universal-reachability theorems at once
(`stateSpace_connected_uncond`). Used as the inductive invariant
maintained through `branch`/`select`/`par`/`rec_` cases. -/
def BothReach (S : SessionType) (env : List (String × Nat)) (start : Nat) : Prop :=
  (∀ k, k < stateCount S → ReflTransGen (edgeRel S start env) start (start + k)) ∧
  (∀ k, k < stateCount S → ReflTransGen (edgeRel S start env) (start + k) (exitSlot S start))

/-!
### List helpers

For the `branch`/`select` case, we iterate across children. We need two
list-level lemmas:

* `childrenRootReach`: from `root` we can reach `childStart + j` for every
  `j < sumChildrenPair ms`, in the `edgeListBranchChildren` graph, provided
  each child satisfies `BothReach`.

* `childrenExitReach`: from `childStart + j` we can reach `bottom` for
  every `j < sumChildrenPair ms`, in the `edgeListBranchChildren` graph,
  provided each child satisfies `BothReach`.
-/

/-- For each child of a branch/select, bundled `BothReach` hypothesis. -/
def allChildrenBothReach (ms : List (String × SessionType))
    (env : List (String × Nat)) : Prop :=
  ∀ (m : String) (s : SessionType), (m, s) ∈ ms →
    ∀ (cs : Nat), BothReach s env cs

/-- Helper: every child-range offset is reachable from `root` in the
`edgeListBranchChildren` graph. -/
theorem childrenRootReach :
    ∀ (ms : List (String × SessionType)) (childStart root bottom : Nat)
      (env : List (String × Nat))
      (_h : allChildrenBothReach ms env)
      (j : Nat),
      j < stateCount.sumChildrenPair ms →
      ReflTransGen
        (fun u v => (u, v) ∈
          edgeList.edgeListBranchChildren ms childStart root bottom env)
        root (childStart + j)
  | [], _, _, _, _, _, j, hj => by
      simp [stateCount.sumChildrenPair] at hj
  | (m, s) :: tl, childStart, root, bottom, env, h, j, hj => by
      simp only [stateCount.sumChildrenPair] at hj
      by_cases hjs : j < stateCount s
      · -- First child
        have hEntry :
            (root, childStart) ∈
              edgeList.edgeListBranchChildren ((m, s) :: tl)
                childStart root bottom env :=
          edgeListBranchChildren_entry m s tl childStart root bottom env
        have hBoth := h m s (by simp) childStart
        have hChild :
            ReflTransGen (edgeRel s childStart env)
              childStart (childStart + j) :=
          hBoth.1 j hjs
        have hChildLifted :
            ReflTransGen
              (fun u v => (u, v) ∈
                edgeList.edgeListBranchChildren ((m, s) :: tl)
                  childStart root bottom env)
              childStart (childStart + j) := by
          refine hChild.mono ?_
          intro u v huv
          exact edgeListBranchChildren_sub_first m s tl childStart root bottom env huv
        exact ReflTransGen.head hEntry hChildLifted
      · push_neg at hjs
        set j' := j - stateCount s with hj'Def
        have hj's : j' < stateCount.sumChildrenPair tl := by omega
        have hjEq : (childStart + stateCount s) + j' = childStart + j := by omega
        have h' : allChildrenBothReach tl env := by
          intro m' s' hmem' cs'
          exact h m' s' (by simp; exact Or.inr hmem') cs'
        have hRest :
            ReflTransGen
              (fun u v => (u, v) ∈ edgeList.edgeListBranchChildren tl
                (childStart + stateCount s) root bottom env)
              root ((childStart + stateCount s) + j') :=
          childrenRootReach tl (childStart + stateCount s) root bottom env h' j' hj's
        have hRestLifted :
            ReflTransGen
              (fun u v => (u, v) ∈
                edgeList.edgeListBranchChildren ((m, s) :: tl)
                  childStart root bottom env)
              root ((childStart + stateCount s) + j') := by
          refine hRest.mono ?_
          intro u v huv
          exact edgeListBranchChildren_sub_rest m s tl childStart root bottom env huv
        rw [hjEq] at hRestLifted
        exact hRestLifted

/-- Helper: every child-range offset reaches `bottom` in the
`edgeListBranchChildren` graph, under `allChildrenBothReach`. -/
theorem childrenExitReach :
    ∀ (ms : List (String × SessionType)) (childStart root bottom : Nat)
      (env : List (String × Nat))
      (_h : allChildrenBothReach ms env)
      (j : Nat),
      j < stateCount.sumChildrenPair ms →
      ReflTransGen
        (fun u v => (u, v) ∈
          edgeList.edgeListBranchChildren ms childStart root bottom env)
        (childStart + j) bottom
  | [], _, _, _, _, _, j, hj => by
      simp [stateCount.sumChildrenPair] at hj
  | (m, s) :: tl, childStart, root, bottom, env, h, j, hj => by
      simp only [stateCount.sumChildrenPair] at hj
      by_cases hjs : j < stateCount s
      · -- First child: walk from (childStart + j) to exitSlot s childStart, then bottom.
        have hBoth := h m s (by simp) childStart
        have hChildExit :
            ReflTransGen (edgeRel s childStart env)
              (childStart + j) (exitSlot s childStart) :=
          hBoth.2 j hjs
        have hChildLifted :
            ReflTransGen
              (fun u v => (u, v) ∈
                edgeList.edgeListBranchChildren ((m, s) :: tl)
                  childStart root bottom env)
              (childStart + j) (exitSlot s childStart) := by
          refine hChildExit.mono ?_
          intro u v huv
          exact edgeListBranchChildren_sub_first m s tl childStart root bottom env huv
        have hExit : (exitSlot s childStart, bottom) ∈
            edgeList.edgeListBranchChildren ((m, s) :: tl) childStart root bottom env :=
          edgeListBranchChildren_exit m s tl childStart root bottom env
        exact hChildLifted.tail hExit
      · push_neg at hjs
        set j' := j - stateCount s with hj'Def
        have hj's : j' < stateCount.sumChildrenPair tl := by omega
        have hjEq : (childStart + stateCount s) + j' = childStart + j := by omega
        have h' : allChildrenBothReach tl env := by
          intro m' s' hmem' cs'
          exact h m' s' (by simp; exact Or.inr hmem') cs'
        have hRest :
            ReflTransGen
              (fun u v => (u, v) ∈ edgeList.edgeListBranchChildren tl
                (childStart + stateCount s) root bottom env)
              ((childStart + stateCount s) + j') bottom :=
          childrenExitReach tl (childStart + stateCount s) root bottom env h' j' hj's
        have hRestLifted :
            ReflTransGen
              (fun u v => (u, v) ∈
                edgeList.edgeListBranchChildren ((m, s) :: tl)
                  childStart root bottom env)
              ((childStart + stateCount s) + j') bottom := by
          refine hRest.mono ?_
          intro u v huv
          exact edgeListBranchChildren_sub_rest m s tl childStart root bottom env huv
        rw [hjEq] at hRestLifted
        exact hRestLifted

/-!
## Main joint theorem (modulo `par`)

We assume a hypothesis `parConnected` for the `par` case and prove the
conjunction for all other constructors.  This is a clean factorisation:
downstream users either discharge `parConnected` via the stride-arithmetic
lemmas (Phase 1b-β1c) or work in the `par`-free fragment.
-/

/-- Hypothesis: `par` satisfies `BothReach` for every arrangement. -/
def ParConnectedHyp : Prop :=
  ∀ (ss : List SessionType) (env : List (String × Nat)) (start : Nat),
    BothReach (.par ss : SessionType) env start

/-!
### sizeOf lemmas for list membership

Lean's auto-generated `sizeOf` on `SessionType` satisfies the following
standard inequalities that we need for well-founded recursion:

* `sizeOf s < sizeOf (.branch ((m, s) :: tl))` for any `m, s, tl`
* `sizeOf s < sizeOf (.branch ms)` for any `(m, s) ∈ ms`
* similarly for `.select`, `.par`, and `.rec_`.

We prove the second (list-membership) form explicitly.
-/

/-- For any pair in a session-type list, its session-type component is
smaller than the list's sum-of-sizes. This is the monomorphic version used
in termination proofs. -/
theorem sizeOf_mem_branch_pair :
    ∀ (ms : List (String × SessionType)) (m : String) (s : SessionType),
      (m, s) ∈ ms → sizeOf s < sizeOf ms
  | (m', s') :: tl, m, s, h => by
      simp only [List.mem_cons] at h
      rcases h with heq | hmem
      · -- (m, s) = (m', s') so s = s'
        rw [Prod.mk.injEq] at heq
        obtain ⟨_, hs⟩ := heq
        subst hs
        simp only [List.cons.sizeOf_spec]
        have : sizeOf (m', s) = 1 + sizeOf m' + sizeOf s := by
          simp [Prod.mk.sizeOf_spec]
        omega
      · have ih := sizeOf_mem_branch_pair tl m s hmem
        simp only [List.cons.sizeOf_spec]
        omega

/-- `sizeOf s < sizeOf (.branch ms)` when `(m, s) ∈ ms`. -/
theorem sizeOf_mem_branch :
    ∀ (ms : List (String × SessionType)) (m : String) (s : SessionType),
      (m, s) ∈ ms → sizeOf s < sizeOf (.branch ms : SessionType) := by
  intro ms m s hmem
  have h := sizeOf_mem_branch_pair ms m s hmem
  -- sizeOf (.branch ms) = 1 + sizeOf ms
  have : sizeOf (.branch ms : SessionType) = 1 + sizeOf ms := by
    simp [SessionType.branch.sizeOf_spec]
  omega

/-- `sizeOf s < sizeOf (.select ls)` when `(m, s) ∈ ls`. -/
theorem sizeOf_mem_select :
    ∀ (ls : List (String × SessionType)) (m : String) (s : SessionType),
      (m, s) ∈ ls → sizeOf s < sizeOf (.select ls : SessionType) := by
  intro ls m s hmem
  have h := sizeOf_mem_branch_pair ls m s hmem
  have : sizeOf (.select ls : SessionType) = 1 + sizeOf ls := by
    simp [SessionType.select.sizeOf_spec]
  omega

/-- `sizeOf body < sizeOf (.rec_ X body)`. -/
theorem sizeOf_rec_body (X : String) (body : SessionType) :
    sizeOf body < sizeOf (.rec_ X body : SessionType) := by
  simp only [SessionType.rec_.sizeOf_spec]
  omega

/-- **Joint reachability theorem (gated by `hPar`).**

For every session type `S`, every environment `env`, and every
offset `start`, the bundle `BothReach S env start` holds: the
root `start` reaches every state in `S`'s range, and every state
in that range reaches `exitSlot S start`.

Proof technique: well-founded recursion on `sizeOf S`. List
children of `branch`/`select` are handled by the helpers
`childrenRootReach` / `childrenExitReach`. The `par` case is taken
as a hypothesis (`hPar : ParConnectedHyp`); the unconditional
version `stateSpace_connected_uncond` discharges `hPar` below. -/
theorem stateSpace_connected (hPar : ParConnectedHyp) :
    ∀ (S : SessionType) (env : List (String × Nat)) (start : Nat),
      BothReach S env start
  | .end_, _, start => by
      refine ⟨?_, ?_⟩
      · intro k hk
        have : k = 0 := by simp [stateCount] at hk; omega
        subst this; simp; exact ReflTransGen.refl
      · intro k hk
        have : k = 0 := by simp [stateCount] at hk; omega
        subst this; simp [exitSlot]; exact ReflTransGen.refl
  | .var _, _, start => by
      refine ⟨?_, ?_⟩
      · intro k hk
        have : k = 0 := by simp [stateCount] at hk; omega
        subst this; simp; exact ReflTransGen.refl
      · intro k hk
        have : k = 0 := by simp [stateCount] at hk; omega
        subst this; simp [exitSlot]; exact ReflTransGen.refl
  | .branch ms, env, start => by
      -- Induction: children satisfy BothReach.
      have hChildren : allChildrenBothReach ms env := by
        intro m s hmem cs
        exact stateSpace_connected hPar s env cs
      refine ⟨?_, ?_⟩
      · -- root reaches all
        intro k hk
        simp only [stateCount] at hk
        rcases Nat.lt_or_ge k 2 with hlt | hge
        · -- k ∈ {0, 1}
          match k, hlt with
          | 0, _ => simp; exact ReflTransGen.refl
          | 1, _ =>
              -- reach bottom = start + 1
              cases hms : ms with
              | nil =>
                  subst hms
                  apply ReflTransGen.single
                  exact edgeList_empty_branch start env
              | cons p tl =>
                  obtain ⟨m, s⟩ := p
                  subst hms
                  -- Entry to first child, then child's exit-reach, then exit edge.
                  have hEntry : (start, start + 2) ∈
                      edgeList (.branch ((m, s) :: tl)) start env := by
                    apply edgeList_branch_of_children
                    exact edgeListBranchChildren_entry m s tl (start + 2)
                            start (start + 1) env
                  have hBoth := hChildren m s (by simp) (start + 2)
                  -- child reaches its own exit from start (k = 0 for child)
                  have hChildToExit :
                      ReflTransGen (edgeRel s (start + 2) env)
                        (start + 2) (exitSlot s (start + 2)) := by
                    have := hBoth.2 0 (stateCount_pos s)
                    simpa using this
                  have hChildLifted :
                      ReflTransGen (edgeRel (.branch ((m, s) :: tl)) start env)
                        (start + 2) (exitSlot s (start + 2)) := by
                    refine hChildToExit.mono ?_
                    intro u v huv
                    apply edgeList_branch_of_children
                    exact edgeListBranchChildren_sub_first m s tl (start + 2)
                      start (start + 1) env huv
                  have hExit : (exitSlot s (start + 2), start + 1) ∈
                      edgeList (.branch ((m, s) :: tl)) start env := by
                    apply edgeList_branch_of_children
                    exact edgeListBranchChildren_exit m s tl (start + 2)
                      start (start + 1) env
                  exact (ReflTransGen.head hEntry hChildLifted).tail hExit
        · -- k ≥ 2
          have hk' : k - 2 < stateCount.sumChildrenPair ms := by omega
          have hEq : start + k = (start + 2) + (k - 2) := by omega
          rw [hEq]
          have :=
            childrenRootReach ms (start + 2) start (start + 1) env hChildren (k - 2) hk'
          refine this.mono ?_
          intro u v huv
          exact edgeList_branch_of_children ms start env huv
      · -- everything reaches exit
        intro k hk
        simp only [stateCount] at hk
        simp only [exitSlot]
        rcases Nat.lt_or_ge k 2 with hlt | hge
        · match k, hlt with
          | 0, _ =>
              -- from start, walk to bottom via (same path as above)
              simp only [Nat.add_zero]
              -- Reuse the k=1 proof path: start → start + 1.
              cases hms : ms with
              | nil =>
                  subst hms
                  apply ReflTransGen.single
                  exact edgeList_empty_branch start env
              | cons p tl =>
                  obtain ⟨m, s⟩ := p
                  subst hms
                  have hEntry : (start, start + 2) ∈
                      edgeList (.branch ((m, s) :: tl)) start env := by
                    apply edgeList_branch_of_children
                    exact edgeListBranchChildren_entry m s tl (start + 2)
                            start (start + 1) env
                  have hBoth := hChildren m s (by simp) (start + 2)
                  have hChildToExit :
                      ReflTransGen (edgeRel s (start + 2) env)
                        (start + 2) (exitSlot s (start + 2)) := by
                    have := hBoth.2 0 (stateCount_pos s)
                    simpa using this
                  have hChildLifted :
                      ReflTransGen (edgeRel (.branch ((m, s) :: tl)) start env)
                        (start + 2) (exitSlot s (start + 2)) := by
                    refine hChildToExit.mono ?_
                    intro u v huv
                    apply edgeList_branch_of_children
                    exact edgeListBranchChildren_sub_first m s tl (start + 2)
                      start (start + 1) env huv
                  have hExit : (exitSlot s (start + 2), start + 1) ∈
                      edgeList (.branch ((m, s) :: tl)) start env := by
                    apply edgeList_branch_of_children
                    exact edgeListBranchChildren_exit m s tl (start + 2)
                      start (start + 1) env
                  exact (ReflTransGen.head hEntry hChildLifted).tail hExit
          | 1, _ =>
              -- from start + 1 = bottom to itself: refl.
              exact ReflTransGen.refl
        · -- k ≥ 2
          have hk' : k - 2 < stateCount.sumChildrenPair ms := by omega
          have hEq : start + k = (start + 2) + (k - 2) := by omega
          rw [hEq]
          have :=
            childrenExitReach ms (start + 2) start (start + 1) env hChildren (k - 2) hk'
          refine this.mono ?_
          intro u v huv
          exact edgeList_branch_of_children ms start env huv
  | .select ls, env, start => by
      have hChildren : allChildrenBothReach ls env := by
        intro m s hmem cs
        exact stateSpace_connected hPar s env cs
      refine ⟨?_, ?_⟩
      · intro k hk
        simp only [stateCount] at hk
        rcases Nat.lt_or_ge k 2 with hlt | hge
        · match k, hlt with
          | 0, _ => simp; exact ReflTransGen.refl
          | 1, _ =>
              cases hls : ls with
              | nil =>
                  subst hls
                  apply ReflTransGen.single
                  exact edgeList_empty_select start env
              | cons p tl =>
                  obtain ⟨m, s⟩ := p
                  subst hls
                  have hEntry : (start, start + 2) ∈
                      edgeList (.select ((m, s) :: tl)) start env := by
                    apply edgeList_select_of_children
                    exact edgeListBranchChildren_entry m s tl (start + 2)
                            start (start + 1) env
                  have hBoth := hChildren m s (by simp) (start + 2)
                  have hChildToExit :
                      ReflTransGen (edgeRel s (start + 2) env)
                        (start + 2) (exitSlot s (start + 2)) := by
                    have := hBoth.2 0 (stateCount_pos s)
                    simpa using this
                  have hChildLifted :
                      ReflTransGen (edgeRel (.select ((m, s) :: tl)) start env)
                        (start + 2) (exitSlot s (start + 2)) := by
                    refine hChildToExit.mono ?_
                    intro u v huv
                    apply edgeList_select_of_children
                    exact edgeListBranchChildren_sub_first m s tl (start + 2)
                      start (start + 1) env huv
                  have hExit : (exitSlot s (start + 2), start + 1) ∈
                      edgeList (.select ((m, s) :: tl)) start env := by
                    apply edgeList_select_of_children
                    exact edgeListBranchChildren_exit m s tl (start + 2)
                      start (start + 1) env
                  exact (ReflTransGen.head hEntry hChildLifted).tail hExit
        · have hk' : k - 2 < stateCount.sumChildrenPair ls := by omega
          have hEq : start + k = (start + 2) + (k - 2) := by omega
          rw [hEq]
          have :=
            childrenRootReach ls (start + 2) start (start + 1) env hChildren (k - 2) hk'
          refine this.mono ?_
          intro u v huv
          exact edgeList_select_of_children ls start env huv
      · intro k hk
        simp only [stateCount] at hk
        simp only [exitSlot]
        rcases Nat.lt_or_ge k 2 with hlt | hge
        · match k, hlt with
          | 0, _ =>
              simp only [Nat.add_zero]
              cases hls : ls with
              | nil =>
                  subst hls
                  apply ReflTransGen.single
                  exact edgeList_empty_select start env
              | cons p tl =>
                  obtain ⟨m, s⟩ := p
                  subst hls
                  have hEntry : (start, start + 2) ∈
                      edgeList (.select ((m, s) :: tl)) start env := by
                    apply edgeList_select_of_children
                    exact edgeListBranchChildren_entry m s tl (start + 2)
                            start (start + 1) env
                  have hBoth := hChildren m s (by simp) (start + 2)
                  have hChildToExit :
                      ReflTransGen (edgeRel s (start + 2) env)
                        (start + 2) (exitSlot s (start + 2)) := by
                    have := hBoth.2 0 (stateCount_pos s)
                    simpa using this
                  have hChildLifted :
                      ReflTransGen (edgeRel (.select ((m, s) :: tl)) start env)
                        (start + 2) (exitSlot s (start + 2)) := by
                    refine hChildToExit.mono ?_
                    intro u v huv
                    apply edgeList_select_of_children
                    exact edgeListBranchChildren_sub_first m s tl (start + 2)
                      start (start + 1) env huv
                  have hExit : (exitSlot s (start + 2), start + 1) ∈
                      edgeList (.select ((m, s) :: tl)) start env := by
                    apply edgeList_select_of_children
                    exact edgeListBranchChildren_exit m s tl (start + 2)
                      start (start + 1) env
                  exact (ReflTransGen.head hEntry hChildLifted).tail hExit
          | 1, _ => exact ReflTransGen.refl
        · have hk' : k - 2 < stateCount.sumChildrenPair ls := by omega
          have hEq : start + k = (start + 2) + (k - 2) := by omega
          rw [hEq]
          have :=
            childrenExitReach ls (start + 2) start (start + 1) env hChildren (k - 2) hk'
          refine this.mono ?_
          intro u v huv
          exact edgeList_select_of_children ls start env huv
  | .par ss, env, start => hPar ss env start
  | .rec_ X body, env, start => by
      -- edgeList (rec_ X body) start env = edgeList body start ((X, start) :: env)
      -- stateCount (rec_ X body) = stateCount body
      -- exitSlot (rec_ X body) start = exitSlot body start
      have hBody := stateSpace_connected hPar body ((X, start) :: env) start
      refine ⟨?_, ?_⟩
      · intro k hk
        have hk' : k < stateCount body := by simp [stateCount] at hk; exact hk
        have h := hBody.1 k hk'
        refine h.mono ?_
        intro u v huv
        show (u, v) ∈ edgeList (.rec_ X body) start env
        simp only [edgeList]
        exact huv
      · intro k hk
        have hk' : k < stateCount body := by simp [stateCount] at hk; exact hk
        have h := hBody.2 k hk'
        -- exitSlot (rec_ X body) start = exitSlot body start
        have hExitEq : exitSlot (.rec_ X body) start = exitSlot body start := by
          simp [exitSlot]
        rw [hExitEq]
        refine h.mono ?_
        intro u v huv
        show (u, v) ∈ edgeList (.rec_ X body) start env
        simp only [edgeList]
        exact huv
termination_by S _ _ => sizeOf S
decreasing_by
  all_goals
    first
    | exact sizeOf_mem_branch _ _ _ hmem
    | exact sizeOf_mem_select _ _ _ hmem
    | exact sizeOf_rec_body _ _

/-!
## Public theorems

We expose the two theorems the downstream bridges want. They take
`parConnected` as an assumption; when callers can discharge it (Phase
1b-β1c lands a proof for `par`), the assumption vanishes.
-/

/-- The root reaches every state (gated form).

For every `S` and every `k < stateCount S`, the index `0` reaches
`k` in `edgeRel S 0 []`. Used to give `[initialState] ≤ [x]` on
the SCC quotient (the `⊥` of the bounded lattice). Proof: the
`.1` projection of `stateSpace_connected hPar S [] 0`. -/
theorem rootReachesAll (hPar : ParConnectedHyp)
    (S : SessionType) (env : List (String × Nat)) (start : Nat)
    (k : Nat) (hk : k < stateCount S) :
    ReflTransGen (edgeRel S start env) start (start + k) :=
  (stateSpace_connected hPar S env start).1 k hk

/-- Every state reaches the exit slot (gated form).

For every `S` and every `k < stateCount S`, the index `k` reaches
`exitSlot S 0` in `edgeRel S 0 []`. Used to give
`[x] ≤ [terminalState]` on the SCC quotient (the `⊤` of the
bounded lattice). Proof: the `.2` projection of
`stateSpace_connected hPar S [] 0`. -/
theorem allReachExit (hPar : ParConnectedHyp)
    (S : SessionType) (env : List (String × Nat)) (start : Nat)
    (k : Nat) (hk : k < stateCount S) :
    ReflTransGen (edgeRel S start env) (start + k) (exitSlot S start) :=
  (stateSpace_connected hPar S env start).2 k hk

/-!
## Partial discharge of `ParConnectedHyp`

The `par []` (empty product) and `par [s]` (singleton) cases are trivial
and we discharge them here. The general `par` case with `|ss| ≥ 2` requires
the suffix-product stride lemmas and is deferred to Phase 1b-β1c.
-/

/-- `par []` satisfies `BothReach`: the graph has exactly one state. -/
theorem bothReach_par_empty (env : List (String × Nat)) (start : Nat) :
    BothReach (.par [] : SessionType) env start := by
  refine ⟨?_, ?_⟩
  · intro k hk
    have : k = 0 := by
      simp only [stateCount, stateCount.prodChildren] at hk
      omega
    subst this
    simp; exact ReflTransGen.refl
  · intro k hk
    have hk0 : k = 0 := by
      simp only [stateCount, stateCount.prodChildren] at hk
      omega
    subst hk0
    -- Goal: ReflTransGen ... (start + 0) (exitSlot (.par []) start)
    -- exitSlot (.par []) start = start + parExitFlat [] = start + 0 = start
    -- So (start + 0) = start = exitSlot
    have hEq : start + 0 = exitSlot (.par [] : SessionType) start := by
      simp [exitSlot, parExitFlat]
    rw [hEq]

/-!
## Phase 1b-β1c-b — full discharge of `ParConnectedHyp`

We prove that every `.par ss` satisfies `BothReach`, unconditional on any
hypothesis, by combining:
* `sizeOf_mem_par` — list-membership size decrease.
* `edgeListParGo_mono_shift` — stride replication lemma.
* `par_cons_bothReach` — combine head child + tail group.
* `par_connected_from_children` — iterate across list.
* `stateSpace_connected_uncond` — well-founded on `sizeOf S`, inlining par.

The primary complication is the internal `filter` inside `edgeListParGo`
(dropping out-of-range var-X edges). We discharge it via:
* `edge_source_in_range` — every edge source is in range.
* `walk_source_in_range` — walks ending in range have in-range starts.
* `walk_lifts_to_filter` — walks between in-range endpoints survive the filter.
-/

/-- `sizeOf` of `.par (s :: tl)` exceeds `sizeOf s`. -/
theorem sizeOf_par_head (s : SessionType) (tl : List SessionType) :
    sizeOf s < sizeOf (.par (s :: tl) : SessionType) := by
  have h1 : sizeOf (.par (s :: tl) : SessionType) = 1 + sizeOf (s :: tl) := by
    simp [SessionType.par.sizeOf_spec]
  have h2 : sizeOf (s :: tl : List SessionType) = 1 + sizeOf s + sizeOf tl := by
    simp [List.cons.sizeOf_spec]
  omega

/-- `sizeOf (.par tl) < sizeOf (.par (s :: tl))`. -/
theorem sizeOf_par_tail (s : SessionType) (tl : List SessionType) :
    sizeOf (.par tl : SessionType) < sizeOf (.par (s :: tl) : SessionType) := by
  have hL : sizeOf (.par tl : SessionType) = 1 + sizeOf tl := by
    simp [SessionType.par.sizeOf_spec]
  have hR : sizeOf (.par (s :: tl) : SessionType) = 1 + sizeOf (s :: tl) := by
    simp [SessionType.par.sizeOf_spec]
  have hC : sizeOf (s :: tl : List SessionType) = 1 + sizeOf s + sizeOf tl := by
    simp [List.cons.sizeOf_spec]
  have hs : 0 < sizeOf s := by
    cases s <;>
      (simp only [SessionType.end_.sizeOf_spec, SessionType.var.sizeOf_spec,
        SessionType.branch.sizeOf_spec, SessionType.select.sizeOf_spec,
        SessionType.par.sizeOf_spec, SessionType.rec_.sizeOf_spec]; omega)
  omega

/-- `sizeOf s < sizeOf (.par ss)` for any `s ∈ ss`. -/
theorem sizeOf_mem_par :
    ∀ (ss : List SessionType) (s : SessionType),
      s ∈ ss → sizeOf s < sizeOf (.par ss : SessionType)
  | s' :: tl, s, h => by
      simp only [List.mem_cons] at h
      rcases h with heq | hmem
      · subst heq; exact sizeOf_par_head s tl
      · have ih := sizeOf_mem_par tl s hmem
        have : sizeOf (.par tl : SessionType) < sizeOf (.par (s' :: tl) : SessionType) :=
          sizeOf_par_tail s' tl
        omega

/-!
### Stride replication lemma

Edges of a child-group `edgeListParGo ys (start + baseIdx * prodChildren ys) env
prefixProdL` embed into `edgeListParGo ys start env prefixProdR`, provided
`baseIdx + prefixProdL ≤ prefixProdR`. Proof by induction on `ys`, using
`mem_edgeListParGo_cons` to peel off the head child.
-/

/-!
### Source-in-range for edges

Every edge emitted by `edgeList S start env` has its source in the allocated
range `[start, start + stateCount S)`. Proof by joint structural recursion
on `S`, its pair-list children (for branch/select), and its list children
(for par). The free `var X` case with `envLookup env X = some n` has target
`n` possibly outside the range, but source = `start` is always in range.
-/

mutual

/-- Source of every edge in `edgeList S start env` lies in `[start, start + stateCount S)`. -/
theorem edge_source_in_range :
    ∀ (S : SessionType) (start : Nat) (env : List (String × Nat))
      (u v : Nat), (u, v) ∈ edgeList S start env →
      start ≤ u ∧ u < start + stateCount S
  | .end_, start, env, u, v, h => by
      simp [edgeList] at h
  | .var X, start, env, u, v, h => by
      simp only [edgeList] at h
      split at h
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        simp only [stateCount]; omega
      · exact (List.not_mem_nil h).elim
  | .branch ms, start, env, u, v, h => by
      simp only [edgeList, List.mem_append] at h
      rcases h with hEmpty | hChildren
      · split at hEmpty
        · simp only [List.mem_singleton, Prod.mk.injEq] at hEmpty
          simp only [stateCount]; omega
        · exact (List.not_mem_nil hEmpty).elim
      · have := edge_source_in_range_branchChildren ms (start + 2) start (start + 1) env
                  u v hChildren
        simp only [stateCount]; rcases this with hL | hR
        · omega
        · omega
  | .select ls, start, env, u, v, h => by
      simp only [edgeList, List.mem_append] at h
      rcases h with hEmpty | hChildren
      · split at hEmpty
        · simp only [List.mem_singleton, Prod.mk.injEq] at hEmpty
          simp only [stateCount]; omega
        · exact (List.not_mem_nil hEmpty).elim
      · have := edge_source_in_range_branchChildren ls (start + 2) start (start + 1) env
                  u v hChildren
        simp only [stateCount]; rcases this with hL | hR
        · omega
        · omega
  | .par ss, start, env, u, v, h => by
      simp only [edgeList] at h
      -- edgeListPar ss start env = edgeListParGo ss start env 1; use mem_edgeListPar.
      have hGo : (u, v) ∈ edgeList.edgeListParGo ss start env 1 :=
        (mem_edgeListPar ss start env u v).mp h
      have := edge_source_in_range_parGo ss start env 1 u v hGo
      simp only [stateCount]; omega
  | .rec_ X body, start, env, u, v, h => by
      simp only [edgeList] at h
      have := edge_source_in_range body start ((X, start) :: env) u v h
      simp only [stateCount]; exact this

/-- Source in range for `edgeListBranchChildren`: either in `[root, root + 2)`
    (entry/exit edges) or in `[childStart, childStart + sumChildrenPair ms)`. -/
theorem edge_source_in_range_branchChildren :
    ∀ (ms : List (String × SessionType)) (childStart root bottom : Nat)
      (env : List (String × Nat)) (u v : Nat),
      (u, v) ∈ edgeList.edgeListBranchChildren ms childStart root bottom env →
      (root ≤ u ∧ u ≤ root + 1) ∨
      (childStart ≤ u ∧ u < childStart + stateCount.sumChildrenPair ms)
  | [],           _,          _,    _,      _,   _, _, h => by
      simp [edgeList.edgeListBranchChildren] at h
  | (_, s) :: tl, childStart, root, bottom, env, u, v, h => by
      -- Structure: (root, childStart) :: (exitSlot s childStart, bottom) ::
      --           edgeList s childStart env ++
      --           edgeListBranchChildren tl (childStart + stateCount s) root bottom env
      have hForm : (u, v) ∈ (root, childStart) ::
                              (exitSlot s childStart, bottom) ::
                              (edgeList s childStart env ++
                               edgeList.edgeListBranchChildren tl
                                 (childStart + stateCount s) root bottom env) := by
        simpa [edgeList.edgeListBranchChildren] using h
      simp only [List.mem_cons, List.mem_append] at hForm
      rcases hForm with hEntry | hExit | hChild | hRest
      · -- (u, v) = (root, childStart)
        rw [Prod.mk.injEq] at hEntry
        obtain ⟨hu, _⟩ := hEntry
        left; omega
      · rw [Prod.mk.injEq] at hExit
        obtain ⟨hu, _⟩ := hExit
        right
        have hexit_lt := exitSlot_lt s childStart
        have hexit_ge := start_le_exitSlot s childStart
        simp only [stateCount.sumChildrenPair]
        omega
      · have := edge_source_in_range s childStart env u v hChild
        right
        simp only [stateCount.sumChildrenPair]
        omega
      · have ih := edge_source_in_range_branchChildren tl (childStart + stateCount s)
                     root bottom env u v hRest
        simp only [stateCount.sumChildrenPair]
        rcases ih with hL | hR
        · left; exact hL
        · right; omega

/-- Source in range for `edgeListParGo`. -/
theorem edge_source_in_range_parGo :
    ∀ (ss : List SessionType) (start : Nat) (env : List (String × Nat))
      (prefixProd : Nat) (u v : Nat),
      (u, v) ∈ edgeList.edgeListParGo ss start env prefixProd →
      start ≤ u ∧ u < start + prefixProd * stateCount.prodChildren ss
  | [],      _,     _,   _,          _, _, h => by
      rw [mem_edgeListParGo_nil] at h
      exact h.elim
  | s :: tl, start, env, prefixProd, u, v, h => by
      rw [mem_edgeListParGo_cons] at h
      simp only at h
      rcases h with hhead | htail
      · rcases (mem_edgeListParLiftChild _ _ _ _ _ _ _).mp hhead with
          ⟨u0, v0, hmem_edge, p, q, hplt, hqlt, hsrc, _⟩
        rw [List.mem_filter] at hmem_edge
        obtain ⟨_, hok⟩ := hmem_edge
        simp at hok
        obtain ⟨hu0, _⟩ := hok
        simp only [stateCount.prodChildren]
        refine ⟨?_, ?_⟩
        · rw [hsrc]; omega
        · rw [hsrc]
          have hstep : u0 * stateCount.prodChildren tl + q
                      < stateCount s * stateCount.prodChildren tl := by
            calc u0 * stateCount.prodChildren tl + q
                < u0 * stateCount.prodChildren tl + stateCount.prodChildren tl := by omega
              _ = (u0 + 1) * stateCount.prodChildren tl := by ring
              _ ≤ stateCount s * stateCount.prodChildren tl :=
                  Nat.mul_le_mul_right _ hu0
          have h1 : p * (stateCount s * stateCount.prodChildren tl) +
                    u0 * stateCount.prodChildren tl + q
                    < prefixProd * (stateCount s * stateCount.prodChildren tl) := by
            calc p * (stateCount s * stateCount.prodChildren tl) +
                  u0 * stateCount.prodChildren tl + q
                < p * (stateCount s * stateCount.prodChildren tl) +
                  stateCount s * stateCount.prodChildren tl := by omega
              _ = (p + 1) * (stateCount s * stateCount.prodChildren tl) := by ring
              _ ≤ prefixProd * (stateCount s * stateCount.prodChildren tl) :=
                  Nat.mul_le_mul_right _ hplt
          omega
      · have ih := edge_source_in_range_parGo tl start env
                     (prefixProd * stateCount s) u v htail
        simp only [stateCount.prodChildren]
        refine ⟨ih.1, ?_⟩
        have heq : prefixProd * stateCount s * stateCount.prodChildren tl
              = prefixProd * (stateCount s * stateCount.prodChildren tl) := by ring
        rw [heq] at ih
        exact ih.2

end

theorem edgeListParGo_mono_shift :
    ∀ (ys : List SessionType) (start : Nat) (env : List (String × Nat))
      (baseIdx prefixProdL prefixProdR : Nat)
      (_hle : baseIdx + prefixProdL ≤ prefixProdR)
      (u v : Nat),
      (u, v) ∈ edgeList.edgeListParGo ys
        (start + baseIdx * stateCount.prodChildren ys) env prefixProdL →
      (u, v) ∈ edgeList.edgeListParGo ys start env prefixProdR
  | [],       _,     _,   _,       _,         _,         _,    _, _ => by
      intro h
      rw [mem_edgeListParGo_nil] at h
      exact h.elim
  | t :: tt, start, env, baseIdx, prefixProdL, prefixProdR, hle, u, v => by
      intro h
      have hPC : stateCount.prodChildren (t :: tt) =
          stateCount t * stateCount.prodChildren tt := by
        simp [stateCount.prodChildren]
      rw [hPC] at h
      rw [mem_edgeListParGo_cons] at h
      simp only at h
      refine (mem_edgeListParGo_cons t tt start env prefixProdR u v).mpr ?_
      simp only
      rcases h with hhead | htail
      · -- Head lift case.
        rcases (mem_edgeListParLiftChild _ _ _ _ _ _ _).mp hhead with
          ⟨u0, v0, hmem_edge, p, q, hplt, hqlt, hsrc, htgt⟩
        refine Or.inl ?_
        refine (mem_edgeListParLiftChild _ _ _ _ _ _ _).mpr ?_
        refine ⟨u0, v0, hmem_edge, baseIdx + p, q, ?_, hqlt, ?_, ?_⟩
        · omega
        · -- u = start + (baseIdx + p) * (size * suffix) + u0 * suffix + q
          -- given hsrc: u = (start + baseIdx*(size*suffix)) + p*(size*suffix) + u0*suffix + q
          have : start + baseIdx * (stateCount t * stateCount.prodChildren tt) +
                   p * (stateCount t * stateCount.prodChildren tt) +
                   u0 * stateCount.prodChildren tt + q =
                 start + (baseIdx + p) * (stateCount t * stateCount.prodChildren tt) +
                   u0 * stateCount.prodChildren tt + q := by ring
          linarith [hsrc]
        · have : start + baseIdx * (stateCount t * stateCount.prodChildren tt) +
                   p * (stateCount t * stateCount.prodChildren tt) +
                   v0 * stateCount.prodChildren tt + q =
                 start + (baseIdx + p) * (stateCount t * stateCount.prodChildren tt) +
                   v0 * stateCount.prodChildren tt + q := by ring
          linarith [htgt]
      · -- Tail recursion case.
        refine Or.inr ?_
        have hreassoc :
            start + baseIdx * (stateCount t * stateCount.prodChildren tt) =
            start + (baseIdx * stateCount t) * stateCount.prodChildren tt := by
          ring
        rw [hreassoc] at htail
        have hle' : baseIdx * stateCount t + prefixProdL * stateCount t ≤
            prefixProdR * stateCount t := by
          have := Nat.mul_le_mul_right (stateCount t) hle
          calc baseIdx * stateCount t + prefixProdL * stateCount t
              = (baseIdx + prefixProdL) * stateCount t := by ring
            _ ≤ prefixProdR * stateCount t := this
        exact edgeListParGo_mono_shift tt start env (baseIdx * stateCount t)
          (prefixProdL * stateCount t) (prefixProdR * stateCount t) hle' u v htail
  termination_by ys _ _ _ _ _ _ _ _ => sizeOf ys

/-!
### Walk confinement: every node whose outgoing walk ends in-range is in-range.
-/

/-- Every node from which a walk reaches an in-range endpoint is in range. -/
theorem walk_source_in_range (S : SessionType) (start : Nat)
    (env : List (String × Nat)) {x y : Nat}
    (hylo : start ≤ y) (hyhi : y < start + stateCount S)
    (hwalk : Relation.ReflTransGen (edgeRel S start env) x y) :
    start ≤ x ∧ x < start + stateCount S := by
  induction hwalk using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨hylo, hyhi⟩
  | head hedge _ _ =>
    exact edge_source_in_range S start env _ _ hedge

/-- Filter lifting: a walk between in-range endpoints uses only edges whose
    endpoints are both in-range, hence survives the filter. -/
theorem walk_lifts_to_filter
    (s : SessionType) (env : List (String × Nat)) {x y : Nat}
    (hyhi : y < stateCount s)
    (hwalk : Relation.ReflTransGen (edgeRel s 0 env) x y) :
    Relation.ReflTransGen
      (fun u v => (u, v) ∈ (edgeList s 0 env).filter
        (fun e => decide (e.1 < stateCount s) && decide (e.2 < stateCount s)))
      x y := by
  -- Induct on walk via head_induction_on. In the head case, we have
  -- an edge (a, c) and rest-walk from c to y.
  induction hwalk using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | head h' hrest ih =>
    -- h' : edgeRel s 0 env a c, i.e., (a, c) ∈ edgeList s 0 env
    -- hrest : ReflTransGen (edgeRel s 0 env) c y
    -- ih : ReflTransGen (filtered) c y
    -- Goal: ReflTransGen (filtered) a y (by extending with (a, c) at head).
    rename_i a c
    have hc_range : (0:Nat) ≤ c ∧ c < 0 + stateCount s :=
      walk_source_in_range s 0 env (Nat.zero_le _) (by omega) hrest
    have ha_range := edge_source_in_range s 0 env _ _ h'
    have hfilter : (a, c) ∈ (edgeList s 0 env).filter
        (fun e => decide (e.1 < stateCount s) && decide (e.2 < stateCount s)) := by
      rw [List.mem_filter]
      refine ⟨h', ?_⟩
      have ha : a < stateCount s := by omega
      have hc : c < stateCount s := by omega
      simp [ha, hc]
    exact Relation.ReflTransGen.head hfilter ih

/-!
## Phase 1b-β1c-b' — combining head + tail into `par (s :: tl)`

We now prove the key combine lemma `par_cons_bothReach`: given `BothReach`
for the head child `s` and for `par tl` (the tail group), conclude
`BothReach (par (s :: tl))`.

Decomposition: `k < stateCount s * prodChildren tl` splits as
`k = qHead * pcTl + rTail` with `qHead < stateCount s`, `rTail < pcTl`.

* Root-reach: `start` ↝ `start + qHead * pcTl` (walk head at tail=0), then
  `start + qHead * pcTl` ↝ `start + qHead * pcTl + rTail` (walk tail at
  head=qHead).
* Exit-reach: `start + qHead * pcTl + rTail` ↝ `start + qHead * pcTl + e_tl`
  (walk tail at head=qHead), then up to
  `start + e_s * pcTl + e_tl = start + parExitFlat (s :: tl)` (walk head at
  tail=e_tl).

Lifting uses `walk_lifts_to_filter` (survives the child-edge filter),
`mem_edgeListParLiftChild` (head-lift), `edgeListParGo_mono_shift` (tail-
replication), and the cons characterisation `mem_edgeListParGo_cons`.
-/

/-- Lift a head-child filtered edge `(u, v) ∈ filtered edgeList s 0 env` into
    `edgeList (.par (s :: tl)) start env` at a fixed tail coordinate `q`.
    The lifted edge is `(start + u * pcTl + q, start + v * pcTl + q)`. -/
theorem lift_head_edge_to_par
    (s : SessionType) (tl : List SessionType)
    (env : List (String × Nat)) (start : Nat)
    (u v : Nat) (q : Nat)
    (hq : q < stateCount.prodChildren tl)
    (hmem : (u, v) ∈ (edgeList s 0 env).filter
      (fun e => decide (e.1 < stateCount s) && decide (e.2 < stateCount s))) :
    (start + u * stateCount.prodChildren tl + q,
     start + v * stateCount.prodChildren tl + q) ∈
      edgeList (.par (s :: tl) : SessionType) start env := by
  -- Unfold edgeList to edgeListPar, then edgeListParGo, then cons peel.
  simp only [edgeList]
  refine (mem_edgeListPar _ _ _ _ _).mpr ?_
  refine (mem_edgeListParGo_cons s tl start env 1 _ _).mpr ?_
  refine Or.inl ?_
  refine (mem_edgeListParLiftChild _ _ _ _ _ _ _).mpr ?_
  refine ⟨u, v, hmem, 0, q, ?_, hq, ?_, ?_⟩
  · exact Nat.zero_lt_one
  · -- src = start + 0 * (size * pcTl) + u * pcTl + q = start + u * pcTl + q
    simp
  · simp

/-- Lift a tail edge `(u, v) ∈ edgeList (.par tl) (start + qHead * pcTl) env`
    into `edgeList (.par (s :: tl)) start env`, provided `qHead < stateCount s`.
    (Uses `edgeListParGo_mono_shift`.) -/
theorem lift_tail_edge_to_par
    (s : SessionType) (tl : List SessionType)
    (env : List (String × Nat)) (start : Nat)
    (qHead : Nat) (hqHead : qHead < stateCount s)
    (u v : Nat)
    (hmem : (u, v) ∈ edgeList (.par tl : SessionType)
              (start + qHead * stateCount.prodChildren tl) env) :
    (u, v) ∈ edgeList (.par (s :: tl) : SessionType) start env := by
  simp only [edgeList] at hmem
  simp only [edgeList]
  refine (mem_edgeListPar _ _ _ _ _).mpr ?_
  refine (mem_edgeListParGo_cons s tl start env 1 _ _).mpr ?_
  refine Or.inr ?_
  -- Now need to match `edgeListParGo tl start env (1 * stateCount s)`.
  have hone : 1 * stateCount s = stateCount s := by ring
  rw [hone]
  -- We have `(u, v) ∈ edgeListPar tl (start + qHead * pcTl) env`, i.e.
  --          `(u, v) ∈ edgeListParGo tl (start + qHead * pcTl) env 1`.
  have hmem' : (u, v) ∈ edgeList.edgeListParGo tl
      (start + qHead * stateCount.prodChildren tl) env 1 :=
    (mem_edgeListPar _ _ _ _ _).mp hmem
  -- Apply `edgeListParGo_mono_shift` with baseIdx = qHead, prefixProdL = 1,
  -- prefixProdR = stateCount s. Need qHead + 1 ≤ stateCount s, i.e. qHead < stateCount s.
  have hle : qHead + 1 ≤ stateCount s := hqHead
  exact edgeListParGo_mono_shift tl start env qHead 1 (stateCount s) hle u v hmem'

/-- Walk in the head coordinate, at a fixed tail coordinate `q`.
    Lifts a walk from `a` to `b` in `edgeList s 0 env` (confined to range)
    into a walk from `start + a * pcTl + q` to `start + b * pcTl + q`
    in `edgeList (.par (s :: tl)) start env`. -/
theorem lift_head_walk_to_par
    (s : SessionType) (tl : List SessionType)
    (env : List (String × Nat)) (start : Nat)
    (q : Nat) (hq : q < stateCount.prodChildren tl)
    {a b : Nat} (hbhi : b < stateCount s)
    (hwalk : ReflTransGen (edgeRel s 0 env) a b) :
    ReflTransGen (edgeRel (.par (s :: tl) : SessionType) start env)
      (start + a * stateCount.prodChildren tl + q)
      (start + b * stateCount.prodChildren tl + q) := by
  -- Confine the walk via the filter, then lift via ReflTransGen.lift.
  have hfiltered := walk_lifts_to_filter s env hbhi hwalk
  -- Use ReflTransGen.lift with f(x) := start + x * pcTl + q.
  have :=
    @Relation.ReflTransGen.lift Nat Nat
      (fun u v => (u, v) ∈ (edgeList s 0 env).filter
        (fun e => decide (e.1 < stateCount s) && decide (e.2 < stateCount s)))
      (edgeRel (.par (s :: tl) : SessionType) start env)
      a b
      (fun x => start + x * stateCount.prodChildren tl + q)
      (fun u v hmem =>
        lift_head_edge_to_par s tl env start u v q hq hmem)
      hfiltered
  exact this

/-- Walk in the tail group, at a fixed head coordinate `qHead`. -/
theorem lift_tail_walk_to_par
    (s : SessionType) (tl : List SessionType)
    (env : List (String × Nat)) (start : Nat)
    (qHead : Nat) (hqHead : qHead < stateCount s)
    {a b : Nat}
    (hwalk : ReflTransGen (edgeRel (.par tl : SessionType)
              (start + qHead * stateCount.prodChildren tl) env) a b) :
    ReflTransGen (edgeRel (.par (s :: tl) : SessionType) start env) a b := by
  -- Lift with f := id: each tail edge is already a par-edge.
  have :=
    @Relation.ReflTransGen.lift Nat Nat
      (edgeRel (.par tl : SessionType)
        (start + qHead * stateCount.prodChildren tl) env)
      (edgeRel (.par (s :: tl) : SessionType) start env)
      a b id
      (fun u v hmem =>
        lift_tail_edge_to_par s tl env start qHead hqHead u v hmem)
      hwalk
  simpa using this

/-- The combine lemma: `BothReach` for the head `s` and for the tail group
    `par tl` implies `BothReach` for `par (s :: tl)`. -/
theorem par_cons_bothReach
    (s : SessionType) (tl : List SessionType)
    (env : List (String × Nat)) (start : Nat)
    (hs : ∀ start', BothReach s env start')
    (htl : ∀ start', BothReach (.par tl : SessionType) env start') :
    BothReach (.par (s :: tl) : SessionType) env start := by
  -- stateCount (par (s :: tl)) = stateCount s * prodChildren tl
  have hSC : stateCount (.par (s :: tl) : SessionType) =
              stateCount s * stateCount.prodChildren tl := by
    simp [stateCount, stateCount.prodChildren]
  -- exitSlot (par (s :: tl)) start = start + exitSlot s 0 * pcTl + parExitFlat tl
  have hExit : exitSlot (.par (s :: tl) : SessionType) start =
               start + exitSlot s 0 * stateCount.prodChildren tl + parExitFlat tl := by
    show start + parExitFlat (s :: tl) = _
    simp [parExitFlat]; ring
  -- Also: exitSlot (par tl) start' = start' + parExitFlat tl
  have hExitTl : ∀ start', exitSlot (.par tl : SessionType) start' =
                   start' + parExitFlat tl := by
    intro start'; simp [exitSlot]
  -- stateCount (par tl) = pcTl
  have hSCTl : stateCount (.par tl : SessionType) = stateCount.prodChildren tl := by
    simp [stateCount]
  -- parExitFlat tl < pcTl (so that we can use it as a tail coordinate).
  have hEtlLt : parExitFlat tl < stateCount.prodChildren tl := parExitFlat_lt tl
  -- pcTl > 0
  have hPcTlPos : 0 < stateCount.prodChildren tl := by
    exact Nat.lt_of_le_of_lt (Nat.zero_le _) hEtlLt
  -- exitSlot s 0 < stateCount s
  have hEsLt : exitSlot s 0 < stateCount s := by
    have := exitSlot_lt s 0; omega
  refine ⟨?_, ?_⟩
  · -- Root-reach
    intro k hk
    rw [hSC] at hk
    -- Decompose k = qHead * pcTl + rTail
    let qHead := k / stateCount.prodChildren tl
    let rTail := k % stateCount.prodChildren tl
    have hqDef : qHead = k / stateCount.prodChildren tl := rfl
    have hrDef : rTail = k % stateCount.prodChildren tl := rfl
    have hkDecomp : k = qHead * stateCount.prodChildren tl + rTail := by
      rw [hqDef, hrDef]
      conv_lhs => rw [← Nat.div_add_mod k (stateCount.prodChildren tl)]
      ring
    have hqHeadLt : qHead < stateCount s := by
      show k / stateCount.prodChildren tl < stateCount s
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hk)
    have hrTailLt : rTail < stateCount.prodChildren tl := Nat.mod_lt k hPcTlPos
    -- Stage 1: start ↝ start + qHead * pcTl (walk head from 0 to qHead, tail = 0)
    have hHeadWalk : ReflTransGen (edgeRel s 0 env) 0 qHead := by
      have := (hs 0).1 qHead hqHeadLt
      simpa using this
    have hHeadLifted :
        ReflTransGen (edgeRel (.par (s :: tl) : SessionType) start env)
          (start + 0 * stateCount.prodChildren tl + 0)
          (start + qHead * stateCount.prodChildren tl + 0) :=
      lift_head_walk_to_par s tl env start 0 hPcTlPos hqHeadLt hHeadWalk
    simp only [Nat.zero_mul, Nat.add_zero] at hHeadLifted
    -- Stage 2: start + qHead * pcTl ↝ start + qHead * pcTl + rTail
    have hTailWalk : ReflTransGen (edgeRel (.par tl : SessionType)
                       (start + qHead * stateCount.prodChildren tl) env)
                       (start + qHead * stateCount.prodChildren tl)
                       (start + qHead * stateCount.prodChildren tl + rTail) := by
      have := (htl (start + qHead * stateCount.prodChildren tl)).1 rTail
        (by rw [hSCTl]; exact hrTailLt)
      exact this
    have hTailLifted :
        ReflTransGen (edgeRel (.par (s :: tl) : SessionType) start env)
          (start + qHead * stateCount.prodChildren tl)
          (start + qHead * stateCount.prodChildren tl + rTail) :=
      lift_tail_walk_to_par s tl env start qHead hqHeadLt hTailWalk
    -- Combine
    have hGoal : start + k = start + qHead * stateCount.prodChildren tl + rTail := by
      rw [hkDecomp]; ring
    rw [hGoal]
    exact hHeadLifted.trans hTailLifted
  · -- Exit-reach
    intro k hk
    rw [hSC] at hk
    let qHead := k / stateCount.prodChildren tl
    let rTail := k % stateCount.prodChildren tl
    have hqDef : qHead = k / stateCount.prodChildren tl := rfl
    have hrDef : rTail = k % stateCount.prodChildren tl := rfl
    have hkDecomp : k = qHead * stateCount.prodChildren tl + rTail := by
      rw [hqDef, hrDef]
      conv_lhs => rw [← Nat.div_add_mod k (stateCount.prodChildren tl)]
      ring
    have hqHeadLt : qHead < stateCount s := by
      show k / stateCount.prodChildren tl < stateCount s
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hk)
    have hrTailLt : rTail < stateCount.prodChildren tl := Nat.mod_lt k hPcTlPos
    -- Stage 1: start + qHead * pcTl + rTail ↝ start + qHead * pcTl + parExitFlat tl
    have hTailWalk : ReflTransGen (edgeRel (.par tl : SessionType)
                       (start + qHead * stateCount.prodChildren tl) env)
                       (start + qHead * stateCount.prodChildren tl + rTail)
                       (exitSlot (.par tl : SessionType)
                          (start + qHead * stateCount.prodChildren tl)) := by
      have := (htl (start + qHead * stateCount.prodChildren tl)).2 rTail
        (by rw [hSCTl]; exact hrTailLt)
      exact this
    rw [hExitTl] at hTailWalk
    have hTailLifted :
        ReflTransGen (edgeRel (.par (s :: tl) : SessionType) start env)
          (start + qHead * stateCount.prodChildren tl + rTail)
          (start + qHead * stateCount.prodChildren tl + parExitFlat tl) :=
      lift_tail_walk_to_par s tl env start qHead hqHeadLt hTailWalk
    -- Stage 2: start + qHead * pcTl + parExitFlat tl ↝ start + exitSlot s 0 * pcTl + parExitFlat tl
    have hHeadWalk : ReflTransGen (edgeRel s 0 env) qHead (exitSlot s 0) := by
      have := (hs 0).2 qHead hqHeadLt
      simpa using this
    have hHeadLifted :
        ReflTransGen (edgeRel (.par (s :: tl) : SessionType) start env)
          (start + qHead * stateCount.prodChildren tl + parExitFlat tl)
          (start + exitSlot s 0 * stateCount.prodChildren tl + parExitFlat tl) :=
      lift_head_walk_to_par s tl env start (parExitFlat tl) hEtlLt hEsLt hHeadWalk
    -- Combine
    have hSrc : start + k = start + qHead * stateCount.prodChildren tl + rTail := by
      rw [hkDecomp]; ring
    rw [hSrc, hExit]
    exact hTailLifted.trans hHeadLifted

/-!
## Discharge of `ParConnectedHyp`

We now discharge `ParConnectedHyp` unconditionally by well-founded
recursion on `sizeOf S`, using `par_cons_bothReach` for the inductive
step and `bothReach_par_empty` for the base case.
-/

/-- The `par` inductive step for the joint reachability theorem.

If every child `s ∈ ss` satisfies `BothReach`, then so does
`par ss`. This is what is needed to discharge the
`ParConnectedHyp` assumption in the gated theorem.

Proof technique: induction on `ss`. The base `[]` case is
`bothReach_par_empty` (par over no children has a single state).
The cons case uses `par_cons_bothReach` which combines the head
child's `BothReach` with the tail's via the lift/unlift family. -/
theorem par_connected_from_children :
    ∀ (ss : List SessionType) (env : List (String × Nat)) (start : Nat),
      (∀ s ∈ ss, ∀ start', BothReach s env start') →
      BothReach (.par ss : SessionType) env start
  | [], env, start, _ => bothReach_par_empty env start
  | s :: tl, env, start, h => by
      refine par_cons_bothReach s tl env start ?_ ?_
      · intro start'
        exact h s (by simp) start'
      · intro start'
        exact par_connected_from_children tl env start'
          (fun s' hmem start'' => h s' (by simp [hmem]) start'')
termination_by ss _ _ _ => sizeOf ss

/-- **Unconditional joint reachability theorem.**

For every session type `S`, every environment, and every offset:
the root reaches every state in `S`'s allocated range, and every
state reaches the exit slot. No `par` hypothesis required.

This is the form actually consumed by
`Reticulate.Spec.StateSpaceLattice.instBoundedOrder` to give the
unconditional `BoundedOrder` on `SCCQuotient (stateSpace S)`. The
statement underwrites `prop:extrema` of §3 of the paper and the
existence of `⊤`/`⊥` in `thm:reticulate`.

Proof technique: structural induction on `S`. The `par` case is
discharged inline using `par_connected_from_children`; the rest
of the cases reuse the gated `stateSpace_connected` shape. -/
theorem stateSpace_connected_uncond :
    ∀ (S : SessionType) (env : List (String × Nat)) (start : Nat),
      BothReach S env start
  | .end_, _, start => by
      refine ⟨?_, ?_⟩
      · intro k hk
        have : k = 0 := by simp [stateCount] at hk; omega
        subst this; simp; exact ReflTransGen.refl
      · intro k hk
        have : k = 0 := by simp [stateCount] at hk; omega
        subst this; simp [exitSlot]; exact ReflTransGen.refl
  | .var _, _, start => by
      refine ⟨?_, ?_⟩
      · intro k hk
        have : k = 0 := by simp [stateCount] at hk; omega
        subst this; simp; exact ReflTransGen.refl
      · intro k hk
        have : k = 0 := by simp [stateCount] at hk; omega
        subst this; simp [exitSlot]; exact ReflTransGen.refl
  | .branch ms, env, start => by
      have hChildren : allChildrenBothReach ms env := by
        intro m s hmem cs
        exact stateSpace_connected_uncond s env cs
      refine ⟨?_, ?_⟩
      · intro k hk
        simp only [stateCount] at hk
        rcases Nat.lt_or_ge k 2 with hlt | hge
        · match k, hlt with
          | 0, _ => simp; exact ReflTransGen.refl
          | 1, _ =>
              cases hms : ms with
              | nil =>
                  subst hms
                  apply ReflTransGen.single
                  exact edgeList_empty_branch start env
              | cons p tl =>
                  obtain ⟨m, s⟩ := p
                  subst hms
                  have hEntry : (start, start + 2) ∈
                      edgeList (.branch ((m, s) :: tl)) start env := by
                    apply edgeList_branch_of_children
                    exact edgeListBranchChildren_entry m s tl (start + 2)
                            start (start + 1) env
                  have hBoth := hChildren m s (by simp) (start + 2)
                  have hChildToExit :
                      ReflTransGen (edgeRel s (start + 2) env)
                        (start + 2) (exitSlot s (start + 2)) := by
                    have := hBoth.2 0 (stateCount_pos s)
                    simpa using this
                  have hChildLifted :
                      ReflTransGen (edgeRel (.branch ((m, s) :: tl)) start env)
                        (start + 2) (exitSlot s (start + 2)) := by
                    refine hChildToExit.mono ?_
                    intro u v huv
                    apply edgeList_branch_of_children
                    exact edgeListBranchChildren_sub_first m s tl (start + 2)
                      start (start + 1) env huv
                  have hExit : (exitSlot s (start + 2), start + 1) ∈
                      edgeList (.branch ((m, s) :: tl)) start env := by
                    apply edgeList_branch_of_children
                    exact edgeListBranchChildren_exit m s tl (start + 2)
                      start (start + 1) env
                  exact (ReflTransGen.head hEntry hChildLifted).tail hExit
        · have hk' : k - 2 < stateCount.sumChildrenPair ms := by omega
          have hEq : start + k = (start + 2) + (k - 2) := by omega
          rw [hEq]
          have :=
            childrenRootReach ms (start + 2) start (start + 1) env hChildren (k - 2) hk'
          refine this.mono ?_
          intro u v huv
          exact edgeList_branch_of_children ms start env huv
      · intro k hk
        simp only [stateCount] at hk
        simp only [exitSlot]
        rcases Nat.lt_or_ge k 2 with hlt | hge
        · match k, hlt with
          | 0, _ =>
              simp only [Nat.add_zero]
              cases hms : ms with
              | nil =>
                  subst hms
                  apply ReflTransGen.single
                  exact edgeList_empty_branch start env
              | cons p tl =>
                  obtain ⟨m, s⟩ := p
                  subst hms
                  have hEntry : (start, start + 2) ∈
                      edgeList (.branch ((m, s) :: tl)) start env := by
                    apply edgeList_branch_of_children
                    exact edgeListBranchChildren_entry m s tl (start + 2)
                            start (start + 1) env
                  have hBoth := hChildren m s (by simp) (start + 2)
                  have hChildToExit :
                      ReflTransGen (edgeRel s (start + 2) env)
                        (start + 2) (exitSlot s (start + 2)) := by
                    have := hBoth.2 0 (stateCount_pos s)
                    simpa using this
                  have hChildLifted :
                      ReflTransGen (edgeRel (.branch ((m, s) :: tl)) start env)
                        (start + 2) (exitSlot s (start + 2)) := by
                    refine hChildToExit.mono ?_
                    intro u v huv
                    apply edgeList_branch_of_children
                    exact edgeListBranchChildren_sub_first m s tl (start + 2)
                      start (start + 1) env huv
                  have hExit : (exitSlot s (start + 2), start + 1) ∈
                      edgeList (.branch ((m, s) :: tl)) start env := by
                    apply edgeList_branch_of_children
                    exact edgeListBranchChildren_exit m s tl (start + 2)
                      start (start + 1) env
                  exact (ReflTransGen.head hEntry hChildLifted).tail hExit
          | 1, _ => exact ReflTransGen.refl
        · have hk' : k - 2 < stateCount.sumChildrenPair ms := by omega
          have hEq : start + k = (start + 2) + (k - 2) := by omega
          rw [hEq]
          have :=
            childrenExitReach ms (start + 2) start (start + 1) env hChildren (k - 2) hk'
          refine this.mono ?_
          intro u v huv
          exact edgeList_branch_of_children ms start env huv
  | .select ls, env, start => by
      have hChildren : allChildrenBothReach ls env := by
        intro m s hmem cs
        exact stateSpace_connected_uncond s env cs
      refine ⟨?_, ?_⟩
      · intro k hk
        simp only [stateCount] at hk
        rcases Nat.lt_or_ge k 2 with hlt | hge
        · match k, hlt with
          | 0, _ => simp; exact ReflTransGen.refl
          | 1, _ =>
              cases hls : ls with
              | nil =>
                  subst hls
                  apply ReflTransGen.single
                  exact edgeList_empty_select start env
              | cons p tl =>
                  obtain ⟨m, s⟩ := p
                  subst hls
                  have hEntry : (start, start + 2) ∈
                      edgeList (.select ((m, s) :: tl)) start env := by
                    apply edgeList_select_of_children
                    exact edgeListBranchChildren_entry m s tl (start + 2)
                            start (start + 1) env
                  have hBoth := hChildren m s (by simp) (start + 2)
                  have hChildToExit :
                      ReflTransGen (edgeRel s (start + 2) env)
                        (start + 2) (exitSlot s (start + 2)) := by
                    have := hBoth.2 0 (stateCount_pos s)
                    simpa using this
                  have hChildLifted :
                      ReflTransGen (edgeRel (.select ((m, s) :: tl)) start env)
                        (start + 2) (exitSlot s (start + 2)) := by
                    refine hChildToExit.mono ?_
                    intro u v huv
                    apply edgeList_select_of_children
                    exact edgeListBranchChildren_sub_first m s tl (start + 2)
                      start (start + 1) env huv
                  have hExit : (exitSlot s (start + 2), start + 1) ∈
                      edgeList (.select ((m, s) :: tl)) start env := by
                    apply edgeList_select_of_children
                    exact edgeListBranchChildren_exit m s tl (start + 2)
                      start (start + 1) env
                  exact (ReflTransGen.head hEntry hChildLifted).tail hExit
        · have hk' : k - 2 < stateCount.sumChildrenPair ls := by omega
          have hEq : start + k = (start + 2) + (k - 2) := by omega
          rw [hEq]
          have :=
            childrenRootReach ls (start + 2) start (start + 1) env hChildren (k - 2) hk'
          refine this.mono ?_
          intro u v huv
          exact edgeList_select_of_children ls start env huv
      · intro k hk
        simp only [stateCount] at hk
        simp only [exitSlot]
        rcases Nat.lt_or_ge k 2 with hlt | hge
        · match k, hlt with
          | 0, _ =>
              simp only [Nat.add_zero]
              cases hls : ls with
              | nil =>
                  subst hls
                  apply ReflTransGen.single
                  exact edgeList_empty_select start env
              | cons p tl =>
                  obtain ⟨m, s⟩ := p
                  subst hls
                  have hEntry : (start, start + 2) ∈
                      edgeList (.select ((m, s) :: tl)) start env := by
                    apply edgeList_select_of_children
                    exact edgeListBranchChildren_entry m s tl (start + 2)
                            start (start + 1) env
                  have hBoth := hChildren m s (by simp) (start + 2)
                  have hChildToExit :
                      ReflTransGen (edgeRel s (start + 2) env)
                        (start + 2) (exitSlot s (start + 2)) := by
                    have := hBoth.2 0 (stateCount_pos s)
                    simpa using this
                  have hChildLifted :
                      ReflTransGen (edgeRel (.select ((m, s) :: tl)) start env)
                        (start + 2) (exitSlot s (start + 2)) := by
                    refine hChildToExit.mono ?_
                    intro u v huv
                    apply edgeList_select_of_children
                    exact edgeListBranchChildren_sub_first m s tl (start + 2)
                      start (start + 1) env huv
                  have hExit : (exitSlot s (start + 2), start + 1) ∈
                      edgeList (.select ((m, s) :: tl)) start env := by
                    apply edgeList_select_of_children
                    exact edgeListBranchChildren_exit m s tl (start + 2)
                      start (start + 1) env
                  exact (ReflTransGen.head hEntry hChildLifted).tail hExit
          | 1, _ => exact ReflTransGen.refl
        · have hk' : k - 2 < stateCount.sumChildrenPair ls := by omega
          have hEq : start + k = (start + 2) + (k - 2) := by omega
          rw [hEq]
          have :=
            childrenExitReach ls (start + 2) start (start + 1) env hChildren (k - 2) hk'
          refine this.mono ?_
          intro u v huv
          exact edgeList_select_of_children ls start env huv
  | .par ss, env, start =>
      par_connected_from_children ss env start
        (fun s _ start' => stateSpace_connected_uncond s env start')
  | .rec_ X body, env, start => by
      have hBody := stateSpace_connected_uncond body ((X, start) :: env) start
      refine ⟨?_, ?_⟩
      · intro k hk
        have hk' : k < stateCount body := by simp [stateCount] at hk; exact hk
        have h := hBody.1 k hk'
        refine h.mono ?_
        intro u v huv
        show (u, v) ∈ edgeList (.rec_ X body) start env
        simp only [edgeList]
        exact huv
      · intro k hk
        have hk' : k < stateCount body := by simp [stateCount] at hk; exact hk
        have h := hBody.2 k hk'
        have hExitEq : exitSlot (.rec_ X body) start = exitSlot body start := by
          simp [exitSlot]
        rw [hExitEq]
        refine h.mono ?_
        intro u v huv
        show (u, v) ∈ edgeList (.rec_ X body) start env
        simp only [edgeList]
        exact huv
termination_by S _ _ => sizeOf S
decreasing_by
  all_goals
    first
    | exact sizeOf_mem_branch _ _ _ hmem
    | exact sizeOf_mem_select _ _ _ hmem
    | exact sizeOf_mem_par _ _ ‹_›
    | exact sizeOf_rec_body _ _

/-- The hypothesis `ParConnectedHyp` is unconditionally true.

This is the discharge that lets us drop the `hPar` argument from
the gated reachability theorems. Proof: instantiate
`stateSpace_connected_uncond` at `par ss`. -/
theorem par_connected : ParConnectedHyp :=
  fun ss env start => stateSpace_connected_uncond (.par ss) env start

/-- **Top reaches everything (unconditional).**

For every `S` and every `k < stateCount S`, the root index `0`
reaches `k` in `edgeRel S 0 []`. This is one half of the
`BoundedOrder` story: `[initialState] ≤ [x]` on the SCC quotient
for every `x`. -/
theorem rootReachesAll_uncond
    (S : SessionType) (env : List (String × Nat)) (start : Nat)
    (k : Nat) (hk : k < stateCount S) :
    ReflTransGen (edgeRel S start env) start (start + k) :=
  (stateSpace_connected_uncond S env start).1 k hk

/-- **Everything reaches the exit (unconditional).**

For every `S` and every `k < stateCount S`, the index `k` reaches
`exitSlot S 0` in `edgeRel S 0 []`. This is the other half of the
`BoundedOrder` story: `[x] ≤ [terminalState]` on the SCC quotient
for every `x`. -/
theorem allReachExit_uncond
    (S : SessionType) (env : List (String × Nat)) (start : Nat)
    (k : Nat) (hk : k < stateCount S) :
    ReflTransGen (edgeRel S start env) (start + k) (exitSlot S start) :=
  (stateSpace_connected_uncond S env start).2 k hk

/-!
## Phase 1b-β3-follow — Structural reachability helpers (Deliverable 1-partial)

These lemmas characterise outgoing-edge structure at the `branch` / `select`
crown. They do **not** yet address target-range (which requires additional
scaffolding on environment validity), but they suffice to establish two
key facts used by downstream cross-child non-reachability arguments:

* **Lemma B (`branch_bottom_no_outgoing`)**: the bottom slot `start + 1`
  emits no edges in `edgeList (.branch ms) start env` — analogously for
  `.select ls`.

* **Lemma C (`branch_root_outgoing`)**: every outgoing edge from the
  root slot `start` has its target at a child's entry offset
  `start + 2 + sumChildrenTake ms i.val` for some child index `i`, or
  (in the empty-branch case) at the bottom slot `start + 1`.

Both lemmas are proved at the `edgeListBranchChildren` helper level and
specialised to `.branch ms` / `.select ls`.

Target-range analysis (Lemma D in the original plan) requires a
companion lemma on `edgeList s childStart env` stating that all targets
fall in `[childStart, childStart + stateCount s)`, which only holds
when `env`'s entries map to offsets inside enclosing graphs — a property
true for `env = []` (top-level) by vacuity but not uniformly when
enclosed by outer `rec_` binders. The follow-up phase will introduce
a `validEnv` predicate and threaded mutual induction to recover it.
-/

/-- Partial sum of `stateCount` over the first `i` children of `ms`. This
is the offset (from `childStart`) at which the `i`-th child begins. -/
def sumChildrenTake :
    List (String × SessionType) → Nat → Nat
  | [],           _     => 0
  | _ :: _,       0     => 0
  | p :: tl,      i + 1 => stateCount p.2 + sumChildrenTake tl i

theorem sumChildrenTake_nil (i : Nat) : sumChildrenTake [] i = 0 := by
  cases i <;> simp [sumChildrenTake]

theorem sumChildrenTake_zero (ms : List (String × SessionType)) :
    sumChildrenTake ms 0 = 0 := by
  cases ms <;> simp [sumChildrenTake]

theorem sumChildrenTake_cons_succ
    (p : String × SessionType) (tl : List (String × SessionType)) (i : Nat) :
    sumChildrenTake (p :: tl) (i + 1) =
      stateCount p.2 + sumChildrenTake tl i := by
  simp [sumChildrenTake]

/-- `sumChildrenTake ms i ≤ sumChildrenPair ms` for every `i`. -/
theorem sumChildrenTake_le :
    ∀ (ms : List (String × SessionType)) (i : Nat),
      sumChildrenTake ms i ≤ stateCount.sumChildrenPair ms
  | [],           _     => by simp [sumChildrenTake_nil, stateCount.sumChildrenPair]
  | _ :: _,       0     => by simp [sumChildrenTake_zero, stateCount.sumChildrenPair]
  | p :: tl,      i + 1 => by
      rw [sumChildrenTake_cons_succ]
      simp only [stateCount.sumChildrenPair]
      have ih := sumChildrenTake_le tl i
      omega

/-- **Lemma B (helper form)**: no edge emitted by
`edgeListBranchChildren ms childStart root bottom env` has source equal
to `bottom`, provided `root < bottom < childStart`. -/
theorem bottom_no_outgoing_branchChildren :
    ∀ (ms : List (String × SessionType)) (childStart root bottom : Nat)
      (env : List (String × Nat)) (v : Nat)
      (_h_lt : root < bottom)
      (_h_sep : bottom < childStart),
      ¬ (bottom, v) ∈
        edgeList.edgeListBranchChildren ms childStart root bottom env
  | [],           _,          _,    _,      _,   _, _, _, h => by
      simp [edgeList.edgeListBranchChildren] at h
  | (_m, s) :: tl, childStart, root, bottom, env, v, hlt, hsep, h => by
      have hForm : (bottom, v) ∈ (root, childStart) ::
                              (exitSlot s childStart, bottom) ::
                              (edgeList s childStart env ++
                               edgeList.edgeListBranchChildren tl
                                 (childStart + stateCount s) root bottom env) := by
        simpa [edgeList.edgeListBranchChildren] using h
      simp only [List.mem_cons, List.mem_append, Prod.mk.injEq] at hForm
      rcases hForm with ⟨hu, _⟩ | ⟨hu, _⟩ | hChild | hRest
      · -- hu : bottom = root, contradicts root < bottom.
        omega
      · -- hu : bottom = exitSlot s childStart ≥ childStart > bottom.
        have hexit_ge := start_le_exitSlot s childStart
        omega
      · -- Edge in child's list: source ≥ childStart > bottom.
        have := edge_source_in_range s childStart env bottom v hChild
        omega
      · -- Recurse on the tail at (childStart + stateCount s).
        have hsep_tl : bottom < childStart + stateCount s := by
          have := stateCount_pos s; omega
        exact bottom_no_outgoing_branchChildren tl
          (childStart + stateCount s) root bottom env v hlt hsep_tl hRest

/-- **Lemma B for `.branch`**: no edge emitted by
`edgeList (.branch ms) start env` has source `start + 1`. -/
theorem branch_bottom_no_outgoing
    (ms : List (String × SessionType)) (start : Nat)
    (env : List (String × Nat)) (v : Nat) :
    ¬ (start + 1, v) ∈ edgeList (.branch ms : SessionType) start env := by
  intro h
  simp only [edgeList, List.mem_append] at h
  rcases h with hEmpty | hChildren
  · split at hEmpty
    · simp only [List.mem_singleton, Prod.mk.injEq] at hEmpty
      omega
    · exact (List.not_mem_nil hEmpty).elim
  · exact bottom_no_outgoing_branchChildren ms (start + 2) start (start + 1) env v
      (by omega) (by omega) hChildren

/-- **Lemma B for `.select`**: no edge emitted by
`edgeList (.select ls) start env` has source `start + 1`. -/
theorem select_bottom_no_outgoing
    (ls : List (String × SessionType)) (start : Nat)
    (env : List (String × Nat)) (v : Nat) :
    ¬ (start + 1, v) ∈ edgeList (.select ls : SessionType) start env := by
  intro h
  simp only [edgeList, List.mem_append] at h
  rcases h with hEmpty | hChildren
  · split at hEmpty
    · simp only [List.mem_singleton, Prod.mk.injEq] at hEmpty
      omega
    · exact (List.not_mem_nil hEmpty).elim
  · exact bottom_no_outgoing_branchChildren ls (start + 2) start (start + 1) env v
      (by omega) (by omega) hChildren

/-- **Lemma C (helper form)**: every outgoing edge from `root` in
`edgeListBranchChildren ms childStart root bottom env` has its target at
a child's entry offset, i.e., of the form `childStart + sumChildrenTake ms i.val`
for some `i : Fin ms.length`. -/
theorem root_outgoing_branchChildren :
    ∀ (ms : List (String × SessionType)) (childStart root bottom : Nat)
      (env : List (String × Nat)) (v : Nat)
      (_h_lt : root < bottom)
      (_h_sep : bottom < childStart)
      (_h : (root, v) ∈
        edgeList.edgeListBranchChildren ms childStart root bottom env),
      ∃ i : Fin ms.length, v = childStart + sumChildrenTake ms i.val
  | [],           _,          _,    _,      _,   _, _, _, h => by
      simp [edgeList.edgeListBranchChildren] at h
  | (m, s) :: tl, childStart, root, bottom, env, v, hlt, hsep, h => by
      have hForm : (root, v) ∈ (root, childStart) ::
                              (exitSlot s childStart, bottom) ::
                              (edgeList s childStart env ++
                               edgeList.edgeListBranchChildren tl
                                 (childStart + stateCount s) root bottom env) := by
        simpa [edgeList.edgeListBranchChildren] using h
      simp only [List.mem_cons, List.mem_append, Prod.mk.injEq] at hForm
      rcases hForm with ⟨_, hv⟩ | ⟨hu, _⟩ | hChild | hRest
      · -- Entry edge: v = childStart. Witness i = 0.
        refine ⟨⟨0, by simp [List.length]⟩, ?_⟩
        rw [sumChildrenTake_zero]
        simp [hv]
      · -- hu : root = exitSlot s childStart ≥ childStart > bottom > root — contradiction.
        have hexit_ge := start_le_exitSlot s childStart
        omega
      · -- source = root in child edges — but those have source ≥ childStart > root.
        have := edge_source_in_range s childStart env root v hChild
        omega
      · -- Tail case.
        have hsep_tl : bottom < childStart + stateCount s := by
          have := stateCount_pos s; omega
        obtain ⟨i, hi⟩ := root_outgoing_branchChildren tl
          (childStart + stateCount s) root bottom env v hlt hsep_tl hRest
        have hlen : i.val + 1 < ((m, s) :: tl).length := by
          simp only [List.length]
          exact Nat.add_lt_add_right i.isLt 1
        refine ⟨⟨i.val + 1, hlen⟩, ?_⟩
        simp only [sumChildrenTake_cons_succ]
        omega

/-- **Lemma C for `.branch`**: every outgoing edge from `start` in
`edgeList (.branch ms) start env` targets either `start + 1` (when
`ms = []`) or a child entry. -/
theorem branch_root_outgoing
    (ms : List (String × SessionType)) (start : Nat)
    (env : List (String × Nat)) (v : Nat)
    (h : (start, v) ∈ edgeList (.branch ms : SessionType) start env) :
    (v = start + 1 ∧ ms = []) ∨
    ∃ i : Fin ms.length, v = (start + 2) + sumChildrenTake ms i.val := by
  simp only [edgeList, List.mem_append] at h
  rcases h with hEmpty | hChildren
  · split at hEmpty
    · rename_i hMs
      simp only [List.mem_singleton, Prod.mk.injEq] at hEmpty
      left
      exact ⟨hEmpty.2, List.isEmpty_iff.mp hMs⟩
    · exact (List.not_mem_nil hEmpty).elim
  · right
    exact root_outgoing_branchChildren ms (start + 2) start (start + 1) env v
      (by omega) (by omega) hChildren

/-- **Lemma C for `.select`**: symmetric statement for selection. -/
theorem select_root_outgoing
    (ls : List (String × SessionType)) (start : Nat)
    (env : List (String × Nat)) (v : Nat)
    (h : (start, v) ∈ edgeList (.select ls : SessionType) start env) :
    (v = start + 1 ∧ ls = []) ∨
    ∃ i : Fin ls.length, v = (start + 2) + sumChildrenTake ls i.val := by
  simp only [edgeList, List.mem_append] at h
  rcases h with hEmpty | hChildren
  · split at hEmpty
    · rename_i hLs
      simp only [List.mem_singleton, Prod.mk.injEq] at hEmpty
      left
      exact ⟨hEmpty.2, List.isEmpty_iff.mp hLs⟩
    · exact (List.not_mem_nil hEmpty).elim
  · right
    exact root_outgoing_branchChildren ls (start + 2) start (start + 1) env v
      (by omega) (by omega) hChildren

/-!
## Phase 1b-β3-follow-2 Part A — Env-aware target-range lemma

The "disjunctive invariant" form: every edge of `edgeList S start env` has
its source in the allocated range `[start, start + stateCount S)`, and its
target is either in the same range or matches some env-bound offset.

This propagates through every constructor cleanly via structural induction
on `S` (with auxiliary inductions on list children for `.branch`, `.select`,
and `.par`).
-/

mutual

/-- **Target-range-or-env** for `edgeList S start env`. Every edge `(u, v)`
emitted has source in `[start, start + stateCount S)` and target either
in `[start, start + stateCount S)` or matching some env-bound offset. -/
theorem edge_target_in_range_or_env :
    ∀ (S : SessionType) (start : Nat) (env : List (String × Nat))
      (u v : Nat), (u, v) ∈ edgeList S start env →
      (start ≤ u ∧ u < start + stateCount S) ∧
      ((start ≤ v ∧ v < start + stateCount S) ∨
       ∃ X, envLookup env X = some v)
  | .end_, start, env, u, v, h => by
      simp [edgeList] at h
  | .var X, start, env, u, v, h => by
      simp only [edgeList] at h
      split at h
      · rename_i hLookup
        simp only [List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨hu, hv⟩ := h
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [hu]
        · rw [hu]
          show start < start + stateCount (.var X : SessionType)
          have hstc : stateCount (.var X : SessionType) = 1 := rfl
          omega
        · right; rw [hv]; exact ⟨X, hLookup⟩
      · exact (List.not_mem_nil h).elim
  | .branch ms, start, env, u, v, h => by
      simp only [edgeList, List.mem_append] at h
      rcases h with hEmpty | hChildren
      · split at hEmpty
        · simp only [List.mem_singleton, Prod.mk.injEq] at hEmpty
          obtain ⟨hu, hv⟩ := hEmpty
          refine ⟨⟨?_, ?_⟩, Or.inl ⟨?_, ?_⟩⟩
          · rw [hu]
          · rw [hu]
            show start < start + stateCount (.branch ms : SessionType)
            have hpos : 0 < stateCount (.branch ms : SessionType) := stateCount_pos _
            omega
          · rw [hv]; omega
          · rw [hv]
            show start + 1 < start + stateCount (.branch ms : SessionType)
            simp only [stateCount]
            have hge : 0 ≤ stateCount.sumChildrenPair ms := Nat.zero_le _
            omega
        · exact (List.not_mem_nil hEmpty).elim
      · have := edge_target_in_range_or_env_branchChildren ms (start + 2) start
                  (start + 1) env u v hChildren (by omega) (by omega)
        refine ⟨?_, ?_⟩
        · simp only [stateCount]; rcases this.1 with hL | hR
          · omega
          · have hsum := sumChildrenTake_le ms ms.length
            omega
        · rcases this.2 with hVL | hVR | hEnv
          · left; simp only [stateCount]; omega
          · left; simp only [stateCount]; omega
          · right; exact hEnv
  | .select ls, start, env, u, v, h => by
      simp only [edgeList, List.mem_append] at h
      rcases h with hEmpty | hChildren
      · split at hEmpty
        · simp only [List.mem_singleton, Prod.mk.injEq] at hEmpty
          obtain ⟨hu, hv⟩ := hEmpty
          refine ⟨⟨?_, ?_⟩, Or.inl ⟨?_, ?_⟩⟩
          · rw [hu]
          · rw [hu]
            show start < start + stateCount (.select ls : SessionType)
            have hpos : 0 < stateCount (.select ls : SessionType) := stateCount_pos _
            omega
          · rw [hv]; omega
          · rw [hv]
            show start + 1 < start + stateCount (.select ls : SessionType)
            simp only [stateCount]
            have hge : 0 ≤ stateCount.sumChildrenPair ls := Nat.zero_le _
            omega
        · exact (List.not_mem_nil hEmpty).elim
      · have := edge_target_in_range_or_env_branchChildren ls (start + 2) start
                  (start + 1) env u v hChildren (by omega) (by omega)
        refine ⟨?_, ?_⟩
        · simp only [stateCount]; rcases this.1 with hL | hR
          · omega
          · have hsum := sumChildrenTake_le ls ls.length
            omega
        · rcases this.2 with hVL | hVR | hEnv
          · left; simp only [stateCount]; omega
          · left; simp only [stateCount]; omega
          · right; exact hEnv
  | .par ss, start, env, u, v, h => by
      -- For par, the filtered child edges guarantee target is in child range,
      -- and the stride arithmetic keeps it within par's range. No env targets.
      simp only [edgeList] at h
      have hGo : (u, v) ∈ edgeList.edgeListParGo ss start env 1 :=
        (mem_edgeListPar ss start env u v).mp h
      have := edge_target_in_range_or_env_parGo ss start env 1 u v hGo
      refine ⟨?_, ?_⟩
      · simp only [stateCount]; omega
      · left; simp only [stateCount]; omega
  | .rec_ X body, start, env, u, v, h => by
      simp only [edgeList] at h
      have := edge_target_in_range_or_env body start ((X, start) :: env) u v h
      refine ⟨?_, ?_⟩
      · simp only [stateCount]; exact this.1
      · rcases this.2 with hIn | ⟨Y, hLookupY⟩
        · left; simp only [stateCount]; exact hIn
        · -- envLookup ((X, start) :: env) Y = some v.
          -- Case split: either Y = X (so v = start, which is in range) or
          -- Y ≠ X (so envLookup env Y = some v, which preserves env witness).
          simp only [envLookup] at hLookupY
          split at hLookupY
          · rename_i hYX
            simp only [Option.some.injEq] at hLookupY
            left
            simp only [stateCount]
            refine ⟨?_, ?_⟩
            · omega
            · have hpos := stateCount_pos body; omega
          · right
            exact ⟨Y, hLookupY⟩

/-- Helper: target-range-or-env for `edgeListBranchChildren`. -/
theorem edge_target_in_range_or_env_branchChildren :
    ∀ (ms : List (String × SessionType)) (childStart root bottom : Nat)
      (env : List (String × Nat)) (u v : Nat),
      (u, v) ∈ edgeList.edgeListBranchChildren ms childStart root bottom env →
      (root < bottom) →
      (bottom < childStart) →
      ((root ≤ u ∧ u ≤ root + 1) ∨
       (childStart ≤ u ∧ u < childStart + stateCount.sumChildrenPair ms)) ∧
      ((u = root ∧ v = root) ∨  -- never occurs, placeholder bucket 1
       ((root ≤ v ∧ v < childStart + stateCount.sumChildrenPair ms)) ∨
       ∃ X, envLookup env X = some v)
  | [],           _,          _,    _,      _,   _, _, h, _, _ => by
      simp [edgeList.edgeListBranchChildren] at h
  | (_m, s) :: tl, childStart, root, bottom, env, u, v, h, hlt, hsep => by
      have hForm : (u, v) ∈ (root, childStart) ::
                              (exitSlot s childStart, bottom) ::
                              (edgeList s childStart env ++
                               edgeList.edgeListBranchChildren tl
                                 (childStart + stateCount s) root bottom env) := by
        simpa [edgeList.edgeListBranchChildren] using h
      simp only [List.mem_cons, List.mem_append, Prod.mk.injEq] at hForm
      rcases hForm with ⟨hu, hv⟩ | ⟨hu, hv⟩ | hChild | hRest
      · -- Entry edge: u = root, v = childStart.
        refine ⟨?_, ?_⟩
        · left; omega
        · right; left
          subst hv
          simp only [stateCount.sumChildrenPair]
          have hpos := stateCount_pos s
          omega
      · -- Exit edge: u = exitSlot s childStart, v = bottom = root + 1.
        have hexit_lt := exitSlot_lt s childStart
        have hexit_ge := start_le_exitSlot s childStart
        refine ⟨?_, ?_⟩
        · right
          simp only [stateCount.sumChildrenPair]
          omega
        · right; left
          subst hv
          simp only [stateCount.sumChildrenPair]
          have hpos := stateCount_pos s
          omega
      · -- Child-internal edge: apply IH.
        have ih := edge_target_in_range_or_env s childStart env u v hChild
        refine ⟨?_, ?_⟩
        · right
          simp only [stateCount.sumChildrenPair]
          omega
        · rcases ih.2 with hIn | hEnv
          · right; left
            simp only [stateCount.sumChildrenPair]
            omega
          · right; right; exact hEnv
      · -- Tail case: apply recursion.
        have hsep_tl : bottom < childStart + stateCount s := by
          have := stateCount_pos s; omega
        have ih := edge_target_in_range_or_env_branchChildren tl
          (childStart + stateCount s) root bottom env u v hRest hlt hsep_tl
        refine ⟨?_, ?_⟩
        · rcases ih.1 with hL | hR
          · left; exact hL
          · right
            simp only [stateCount.sumChildrenPair]
            omega
        · rcases ih.2 with hUV | hIn | hEnv
          · exact Or.inl hUV
          · right; left
            simp only [stateCount.sumChildrenPair]
            omega
          · right; right; exact hEnv

/-- Helper: target-range-or-env for `edgeListParGo`. For par, all targets
are in range (no env leakage due to filter inside the lift). -/
theorem edge_target_in_range_or_env_parGo :
    ∀ (ss : List SessionType) (start : Nat) (env : List (String × Nat))
      (prefixProd : Nat) (u v : Nat),
      (u, v) ∈ edgeList.edgeListParGo ss start env prefixProd →
      (start ≤ u ∧ u < start + prefixProd * stateCount.prodChildren ss) ∧
      (start ≤ v ∧ v < start + prefixProd * stateCount.prodChildren ss)
  | [],      _,     _,   _,          _, _, h => by
      rw [mem_edgeListParGo_nil] at h
      exact h.elim
  | s :: tl, start, env, prefixProd, u, v, h => by
      rw [mem_edgeListParGo_cons] at h
      simp only at h
      rcases h with hhead | htail
      · rcases (mem_edgeListParLiftChild _ _ _ _ _ _ _).mp hhead with
          ⟨u0, v0, hmem_edge, p, q, hplt, hqlt, hsrc, htgt⟩
        rw [List.mem_filter] at hmem_edge
        obtain ⟨_, hok⟩ := hmem_edge
        simp at hok
        obtain ⟨hu0, hv0⟩ := hok
        simp only [stateCount.prodChildren]
        refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
        · rw [hsrc]; omega
        · rw [hsrc]
          have hstep : u0 * stateCount.prodChildren tl + q
                      < stateCount s * stateCount.prodChildren tl := by
            calc u0 * stateCount.prodChildren tl + q
                < u0 * stateCount.prodChildren tl + stateCount.prodChildren tl := by omega
              _ = (u0 + 1) * stateCount.prodChildren tl := by ring
              _ ≤ stateCount s * stateCount.prodChildren tl :=
                  Nat.mul_le_mul_right _ hu0
          have h1 : p * (stateCount s * stateCount.prodChildren tl) +
                    u0 * stateCount.prodChildren tl + q
                    < prefixProd * (stateCount s * stateCount.prodChildren tl) := by
            calc p * (stateCount s * stateCount.prodChildren tl) +
                  u0 * stateCount.prodChildren tl + q
                < p * (stateCount s * stateCount.prodChildren tl) +
                  stateCount s * stateCount.prodChildren tl := by omega
              _ = (p + 1) * (stateCount s * stateCount.prodChildren tl) := by ring
              _ ≤ prefixProd * (stateCount s * stateCount.prodChildren tl) :=
                  Nat.mul_le_mul_right _ hplt
          omega
        · rw [htgt]; omega
        · rw [htgt]
          have hstep : v0 * stateCount.prodChildren tl + q
                      < stateCount s * stateCount.prodChildren tl := by
            calc v0 * stateCount.prodChildren tl + q
                < v0 * stateCount.prodChildren tl + stateCount.prodChildren tl := by omega
              _ = (v0 + 1) * stateCount.prodChildren tl := by ring
              _ ≤ stateCount s * stateCount.prodChildren tl :=
                  Nat.mul_le_mul_right _ hv0
          have h1 : p * (stateCount s * stateCount.prodChildren tl) +
                    v0 * stateCount.prodChildren tl + q
                    < prefixProd * (stateCount s * stateCount.prodChildren tl) := by
            calc p * (stateCount s * stateCount.prodChildren tl) +
                  v0 * stateCount.prodChildren tl + q
                < p * (stateCount s * stateCount.prodChildren tl) +
                  stateCount s * stateCount.prodChildren tl := by omega
              _ = (p + 1) * (stateCount s * stateCount.prodChildren tl) := by ring
              _ ≤ prefixProd * (stateCount s * stateCount.prodChildren tl) :=
                  Nat.mul_le_mul_right _ hplt
          omega
      · have ih := edge_target_in_range_or_env_parGo tl start env
                     (prefixProd * stateCount s) u v htail
        simp only [stateCount.prodChildren]
        have heq : prefixProd * stateCount s * stateCount.prodChildren tl
              = prefixProd * (stateCount s * stateCount.prodChildren tl) := by ring
        rw [heq] at ih
        exact ih

end

/-- **Specialisation to `env = []`**: every edge of `edgeList S 0 []` has
both endpoints in `[0, stateCount S)`. The env tail vanishes because
`envLookup [] X = none` always. -/
theorem edge_target_in_range_nil
    (S : SessionType) (u v : Nat)
    (h : (u, v) ∈ edgeList S 0 []) :
    u < stateCount S ∧ v < stateCount S := by
  have hAll := edge_target_in_range_or_env S 0 [] u v h
  refine ⟨?_, ?_⟩
  · have := hAll.1; omega
  · rcases hAll.2 with hIn | ⟨X, hLookup⟩
    · omega
    · -- envLookup [] X = none always, contradiction with some v.
      have hNone : envLookup [] X = none := rfl
      rw [hNone] at hLookup
      cases hLookup

/-!
## Phase 1b-β3-follow-2 Part B — Branch/select edge taxonomy

Exact classification of edges emitted by `edgeList (.branch ms) 0 []`:
four mutually exclusive buckets — empty-branch root→bottom, root→child
entry, child-exit→bottom, and child-internal.

Strategy: we prove the taxonomy for the helper `edgeListBranchChildren ms
childStart 0 1 []` by induction on `ms`, peeling one child at a time and
bumping `childStart` by `stateCount s`. The `sumChildrenTake` witness
emerges naturally as the accumulated offset.
-/

/-- **Helper for branch edge taxonomy** at the `edgeListBranchChildren` level.
Given `(u, v) ∈ edgeListBranchChildren ms childStart 0 1 []`, the edge
falls into one of three buckets: entry (u=0), exit (v=1), or child-internal
with the child edge unshifted (since we work with absolute indices already). -/
private theorem branchChildren_edge_taxonomy :
    ∀ (ms : List (String × SessionType)) (childStart : Nat) (u v : Nat),
      (u, v) ∈ edgeList.edgeListBranchChildren ms childStart 0 1 [] →
      (u = 0 ∧ ∃ i : Fin ms.length,
        v = childStart + sumChildrenTake ms i.val)
      ∨ (v = 1 ∧ ∃ i : Fin ms.length,
        u = exitSlot (ms.get i).2 (childStart + sumChildrenTake ms i.val))
      ∨ (∃ i : Fin ms.length,
        (childStart + sumChildrenTake ms i.val) ≤ u ∧
        u < (childStart + sumChildrenTake ms i.val) + stateCount (ms.get i).2 ∧
        (childStart + sumChildrenTake ms i.val) ≤ v ∧
        v < (childStart + sumChildrenTake ms i.val) + stateCount (ms.get i).2 ∧
        (u, v) ∈ edgeList (ms.get i).2
            (childStart + sumChildrenTake ms i.val) [])
  | [],           _,          _, _, h => by
      simp [edgeList.edgeListBranchChildren] at h
  | (_m, s) :: tl, childStart, u, v, h => by
      have hForm : (u, v) ∈ (0, childStart) ::
                              (exitSlot s childStart, 1) ::
                              (edgeList s childStart [] ++
                               edgeList.edgeListBranchChildren tl
                                 (childStart + stateCount s) 0 1 []) := by
        simpa [edgeList.edgeListBranchChildren] using h
      simp only [List.mem_cons, List.mem_append, Prod.mk.injEq] at hForm
      rcases hForm with ⟨hu, hv⟩ | ⟨hu, hv⟩ | hChild | hRest
      · -- Entry edge: u = 0, v = childStart. Witness i = 0 (head child).
        left
        have hlen : (0 : Nat) < ((_m, s) :: tl).length := by
          simp [List.length]
        refine ⟨hu, ⟨0, hlen⟩, ?_⟩
        show v = childStart + sumChildrenTake ((_m, s) :: tl) 0
        rw [sumChildrenTake_zero]
        omega
      · -- Exit edge: u = exitSlot s childStart, v = 1. Witness i = 0.
        right; left
        have hlen : (0 : Nat) < ((_m, s) :: tl).length := by
          simp [List.length]
        refine ⟨hv, ⟨0, hlen⟩, ?_⟩
        show u = exitSlot (((_m, s) :: tl).get ⟨0, hlen⟩).2
                  (childStart + sumChildrenTake ((_m, s) :: tl) 0)
        rw [sumChildrenTake_zero]
        have hget : (((_m, s) :: tl).get ⟨0, hlen⟩).2 = s := rfl
        rw [hget]
        have : childStart + 0 = childStart := by omega
        rw [this]
        exact hu
      · -- Child-internal edge of head s.
        right; right
        have hlen : (0 : Nat) < ((_m, s) :: tl).length := by
          simp [List.length]
        have hget : (((_m, s) :: tl).get ⟨0, hlen⟩).2 = s := rfl
        have hsrc := edge_source_in_range s childStart [] u v hChild
        have htgt := edge_target_in_range_or_env s childStart [] u v hChild
        refine ⟨⟨0, hlen⟩, ?_, ?_, ?_, ?_, ?_⟩
        · show childStart + sumChildrenTake ((_m, s) :: tl) 0 ≤ u
          rw [sumChildrenTake_zero]; omega
        · show u < childStart + sumChildrenTake ((_m, s) :: tl) 0 +
                    stateCount (((_m, s) :: tl).get ⟨0, hlen⟩).2
          rw [sumChildrenTake_zero, hget]; omega
        · show childStart + sumChildrenTake ((_m, s) :: tl) 0 ≤ v
          rw [sumChildrenTake_zero]
          rcases htgt.2 with hIn | ⟨X, hLookup⟩
          · omega
          · have hNone : envLookup [] X = none := rfl
            rw [hNone] at hLookup
            cases hLookup
        · show v < childStart + sumChildrenTake ((_m, s) :: tl) 0 +
                    stateCount (((_m, s) :: tl).get ⟨0, hlen⟩).2
          rw [sumChildrenTake_zero, hget]
          rcases htgt.2 with hIn | ⟨X, hLookup⟩
          · omega
          · have hNone : envLookup [] X = none := rfl
            rw [hNone] at hLookup
            cases hLookup
        · show (u, v) ∈ edgeList (((_m, s) :: tl).get ⟨0, hlen⟩).2
              (childStart + sumChildrenTake ((_m, s) :: tl) 0) []
          rw [sumChildrenTake_zero, hget]
          have : childStart + 0 = childStart := by omega
          rw [this]
          exact hChild
      · -- Tail case: recurse, then shift index by 1.
        have ih := branchChildren_edge_taxonomy tl (childStart + stateCount s) u v hRest
        rcases ih with ⟨hu_eq, i, hv_eq⟩
                     | ⟨hv_eq, i, hu_eq⟩
                     | ⟨i, hu_lo, hu_hi, hv_lo, hv_hi, hmem⟩
        · left
          have hlen : i.val + 1 < ((_m, s) :: tl).length := by
            have := i.isLt
            simp only [List.length_cons]; omega
          -- hv_eq has type: v = (childStart + stateCount s) + sumChildrenTake tl i.val
          refine ⟨hu_eq, ⟨i.val + 1, hlen⟩, ?_⟩
          show v = childStart + sumChildrenTake ((_m, s) :: tl) (i.val + 1)
          rw [sumChildrenTake_cons_succ]
          rw [hv_eq]; ring
        · right; left
          have hlen : i.val + 1 < ((_m, s) :: tl).length := by
            have := i.isLt
            simp only [List.length_cons]; omega
          refine ⟨hv_eq, ⟨i.val + 1, hlen⟩, ?_⟩
          show u = exitSlot (((_m, s) :: tl).get ⟨i.val + 1, hlen⟩).2
            (childStart + sumChildrenTake ((_m, s) :: tl) (i.val + 1))
          rw [sumChildrenTake_cons_succ]
          have hget : (((_m, s) :: tl).get ⟨i.val + 1, hlen⟩).2 =
                      (tl.get i).2 := rfl
          rw [hget]
          have : childStart + (stateCount s + sumChildrenTake tl i.val) =
                 childStart + stateCount s + sumChildrenTake tl i.val := by omega
          rw [this]
          exact hu_eq
        · right; right
          have hlen : i.val + 1 < ((_m, s) :: tl).length := by
            have := i.isLt
            simp only [List.length_cons]; omega
          have hget : (((_m, s) :: tl).get ⟨i.val + 1, hlen⟩).2 =
                      (tl.get i).2 := rfl
          have hrw : childStart + (stateCount s + sumChildrenTake tl i.val) =
                     childStart + stateCount s + sumChildrenTake tl i.val := by omega
          -- IH gives hu_lo, hu_hi, hv_lo, hv_hi using (childStart + stateCount s)
          -- as the base. We rewrite them to match (childStart + (stateCount s + ...)).
          refine ⟨⟨i.val + 1, hlen⟩, ?_, ?_, ?_, ?_, ?_⟩
          · show childStart + sumChildrenTake ((_m, s) :: tl) (i.val + 1) ≤ u
            rw [sumChildrenTake_cons_succ, hrw]
            exact hu_lo
          · show u < childStart + sumChildrenTake ((_m, s) :: tl) (i.val + 1) +
                      stateCount (((_m, s) :: tl).get ⟨i.val + 1, hlen⟩).2
            rw [sumChildrenTake_cons_succ, hget, hrw]
            exact hu_hi
          · show childStart + sumChildrenTake ((_m, s) :: tl) (i.val + 1) ≤ v
            rw [sumChildrenTake_cons_succ, hrw]
            exact hv_lo
          · show v < childStart + sumChildrenTake ((_m, s) :: tl) (i.val + 1) +
                      stateCount (((_m, s) :: tl).get ⟨i.val + 1, hlen⟩).2
            rw [sumChildrenTake_cons_succ, hget, hrw]
            exact hv_hi
          · show (u, v) ∈ edgeList (((_m, s) :: tl).get ⟨i.val + 1, hlen⟩).2
              (childStart + sumChildrenTake ((_m, s) :: tl) (i.val + 1)) []
            rw [sumChildrenTake_cons_succ, hget, hrw]
            exact hmem

/-- **Branch edge taxonomy.** Every edge of `edgeList (.branch ms) 0 []` falls into exactly one of three classes.
falls into one of four disjoint buckets. -/
theorem branch_edge_taxonomy
    (ms : List (String × SessionType)) (u v : Nat)
    (h : (u, v) ∈ edgeList (.branch ms : SessionType) 0 []) :
    (u = 0 ∧ v = 1 ∧ ms = [])
    ∨ (u = 0 ∧ ∃ i : Fin ms.length,
        v = 2 + (sumChildrenTake ms i.val))
    ∨ (v = 1 ∧ ∃ i : Fin ms.length,
        u = exitSlot (ms.get i).2 (2 + sumChildrenTake ms i.val))
    ∨ (∃ i : Fin ms.length,
        (2 + sumChildrenTake ms i.val) ≤ u ∧
        u < (2 + sumChildrenTake ms i.val) + stateCount (ms.get i).2 ∧
        (2 + sumChildrenTake ms i.val) ≤ v ∧
        v < (2 + sumChildrenTake ms i.val) + stateCount (ms.get i).2 ∧
        (u, v) ∈ edgeList (ms.get i).2 (2 + sumChildrenTake ms i.val) []) := by
  simp only [edgeList, List.mem_append] at h
  rcases h with hEmpty | hChildren
  · -- Empty-branch bucket.
    split at hEmpty
    · rename_i hMs
      simp only [List.mem_singleton, Prod.mk.injEq] at hEmpty
      left
      exact ⟨hEmpty.1, hEmpty.2, List.isEmpty_iff.mp hMs⟩
    · exact (List.not_mem_nil hEmpty).elim
  · -- Children bucket: apply the helper at childStart = 2.
    have : (0 + 2) = 2 := by omega
    have hChildren' : (u, v) ∈ edgeList.edgeListBranchChildren ms 2 0 1 [] := by
      convert hChildren using 1
    have := branchChildren_edge_taxonomy ms 2 u v hChildren'
    rcases this with ⟨hu_eq, i, hv_eq⟩
                   | ⟨hv_eq, i, hu_eq⟩
                   | ⟨i, hu_lo, hu_hi, hv_lo, hv_hi, hmem⟩
    · right; left
      exact ⟨hu_eq, i, hv_eq⟩
    · right; right; left
      exact ⟨hv_eq, i, hu_eq⟩
    · right; right; right
      exact ⟨i, hu_lo, hu_hi, hv_lo, hv_hi, hmem⟩

/-- **Select edge taxonomy**: identical to branch, since the edge list is
produced by the same `edgeListBranchChildren` helper. -/
theorem select_edge_taxonomy
    (ls : List (String × SessionType)) (u v : Nat)
    (h : (u, v) ∈ edgeList (.select ls : SessionType) 0 []) :
    (u = 0 ∧ v = 1 ∧ ls = [])
    ∨ (u = 0 ∧ ∃ i : Fin ls.length,
        v = 2 + (sumChildrenTake ls i.val))
    ∨ (v = 1 ∧ ∃ i : Fin ls.length,
        u = exitSlot (ls.get i).2 (2 + sumChildrenTake ls i.val))
    ∨ (∃ i : Fin ls.length,
        (2 + sumChildrenTake ls i.val) ≤ u ∧
        u < (2 + sumChildrenTake ls i.val) + stateCount (ls.get i).2 ∧
        (2 + sumChildrenTake ls i.val) ≤ v ∧
        v < (2 + sumChildrenTake ls i.val) + stateCount (ls.get i).2 ∧
        (u, v) ∈ edgeList (ls.get i).2 (2 + sumChildrenTake ls i.val) []) := by
  simp only [edgeList, List.mem_append] at h
  rcases h with hEmpty | hChildren
  · split at hEmpty
    · rename_i hLs
      simp only [List.mem_singleton, Prod.mk.injEq] at hEmpty
      left
      exact ⟨hEmpty.1, hEmpty.2, List.isEmpty_iff.mp hLs⟩
    · exact (List.not_mem_nil hEmpty).elim
  · have hChildren' : (u, v) ∈ edgeList.edgeListBranchChildren ls 2 0 1 [] := by
      convert hChildren using 1
    have := branchChildren_edge_taxonomy ls 2 u v hChildren'
    rcases this with ⟨hu_eq, i, hv_eq⟩
                   | ⟨hv_eq, i, hu_eq⟩
                   | ⟨i, hu_lo, hu_hi, hv_lo, hv_hi, hmem⟩
    · right; left
      exact ⟨hu_eq, i, hv_eq⟩
    · right; right; left
      exact ⟨hv_eq, i, hu_eq⟩
    · right; right; right
      exact ⟨i, hu_lo, hu_hi, hv_lo, hv_hi, hmem⟩

end SessionType

end Reticulate.Spec
