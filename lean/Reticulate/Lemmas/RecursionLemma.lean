/-
Copyright (c) 2026 Alexandre Zua Caldeira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexandre Zua Caldeira
-/
import Reticulate.Lemmas.BottomAbsorption
import Reticulate.Graph.SCC

/-!
# Recursion Lemma

Proves that `rec X.S` preserves bounded lattice structure on session type
state spaces, by reducing to the Bottom Absorption Lemma.

This formalizes Lemma 6 from "Session Type State Spaces Form Lattices"
(Caldeira & Vasconcelos, 2026).

## Setup

Given:
- A finite directed graph G_body representing the state space of the body S.
- The SCC quotient of G_body forms a bounded lattice (with OrderBot and OrderTop).
- A set of "variable states" V_X (occurrences of X in S).
- An initial state q_bot that can reach all other states.
- Back-edges from each v ∈ V_X to q_bot (the recursion construction).

## Main result

* `Reticulate.recursion_preserves_lattice`: The SCC quotient of the graph
  with back-edges added admits a bounded lattice structure.

## Proof structure

1. `absorbed_lower_closed`: The absorbed set D is downward-closed (IsLowerSet).
2. Helper lemmas lift body-graph paths to the recursive graph and characterize
   non-absorbed mutual reachability.
3. An order-preserving bijection φ/ψ between SCCQuotient(recGraph) and the
   Bottom Absorption quotient L'(D) transfers the lattice structure.
-/

open Classical
noncomputable section

namespace Reticulate

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The hypotheses for the recursion lemma. -/
structure RecursionSetup (V : Type*) [Fintype V] [DecidableEq V] where
  /-- The body graph (state space of S). -/
  bodyGraph : FinDiGraph V
  /-- The initial state (q_bot^S). -/
  initial : V
  /-- The variable states (occurrences of X). -/
  varStates : Finset V
  /-- The initial state reaches every other state. -/
  initial_reaches_all : ∀ (v : V), Reachable bodyGraph initial v
  /-- The SCC quotient of the body has a lattice structure. -/
  bodyLattice : Lattice (SCCQuotient bodyGraph)
  /-- The SCC quotient of the body has a bottom (initial state's class). -/
  bodyOrderBot : OrderBot (SCCQuotient bodyGraph)
  /-- The SCC quotient of the body has a top. -/
  bodyOrderTop : OrderTop (SCCQuotient bodyGraph)
  /-- The initial state is the bottom of the body's quotient lattice. -/
  initial_is_bot :
    @Eq (SCCQuotient bodyGraph)
      (⟦initial⟧)
      (@Bot.bot (SCCQuotient bodyGraph) bodyOrderBot.toBot)
  /-- The lattice ordering agrees with the reachability ordering (coherence).
      This ensures that the Lattice instance on SCCQuotient bodyGraph is
      compatible with the canonical PartialOrder from reachability. -/
  body_le_iff_reach : ∀ (u v : V),
    @LE.le (SCCQuotient bodyGraph)
      (bodyLattice.toSemilatticeInf.toPartialOrder.toPreorder.toLE)
      (⟦u⟧ : SCCQuotient bodyGraph) (⟦v⟧ : SCCQuotient bodyGraph) ↔
    Reachable bodyGraph u v

/-- The recursive graph: body graph plus back-edges from variable states to initial. -/
def RecursionSetup.recGraph (setup : RecursionSetup V) : FinDiGraph V where
  edge u v := setup.bodyGraph.edge u v ∨ (u ∈ setup.varStates ∧ v = setup.initial)
  edge_decidable := inferInstance

/-- In the recursive graph, each variable state is mutually reachable with
    the initial state. -/
theorem RecursionSetup.var_mutual_initial (setup : RecursionSetup V)
    (v : V) (hv : v ∈ setup.varStates) :
    MutuallyReachable setup.recGraph setup.initial v := by
  constructor
  · -- initial reaches v: body graph paths lift to recGraph
    have hbody := setup.initial_reaches_all v
    exact Relation.ReflTransGen.mono (fun x y h => Or.inl h) hbody
  · -- v reaches initial: via the back-edge
    apply Reachable.single
    exact Or.inr ⟨hv, rfl⟩

/-- The absorbed set: SCC classes in the body quotient that merge with the initial
    state's class in the recursive graph. -/
def RecursionSetup.absorbedSet (setup : RecursionSetup V) :
    Set (SCCQuotient setup.bodyGraph) :=
  { cls | ∃ (s : V), (⟦s⟧ : SCCQuotient setup.bodyGraph) = cls ∧
    MutuallyReachable setup.recGraph s setup.initial }

/-- The absorbed set contains ⊥ (the initial state's class). -/
theorem RecursionSetup.bot_mem_absorbed (setup : RecursionSetup V) :
    @Bot.bot _ setup.bodyOrderBot.toBot ∈ setup.absorbedSet := by
  rw [← setup.initial_is_bot]
  exact ⟨setup.initial, rfl, MutuallyReachable.refl _ _⟩

/-- The absorbed set is downward-closed in the body's quotient ordering.

    Proof sketch: If [s] ∈ D and [r] ≤ [s] in the body quotient, then:
    - q_bot reaches r (by initial_reaches_all)
    - r reaches s (by [r] ≤ [s], unwinding quotient ordering)
    - s reaches q_bot (since [s] ∈ D)
    - Therefore r ↔ q_bot in G_rec, hence [r] ∈ D.

    Key step: unwinding the quotient ordering to get a concrete path from
    r to s in the body graph, then lifting it to the recursive graph. -/
theorem RecursionSetup.absorbed_lower_closed (setup : RecursionSetup V) :
    IsLowerSet setup.absorbedSet := by
  -- IsLowerSet: ∀ ⦃a b⦄, b ≤ a → a ∈ s → b ∈ s
  -- a is upper (known in D), b is lower (to prove in D)
  intro a b hab ha
  obtain ⟨s, hs_eq, hs_mutual⟩ := ha
  -- Eliminate b to a concrete representative r
  revert hab
  refine Quotient.inductionOn b (fun r hab => ?_)
  -- Now hab : ⟦r⟧ ≤ a, substitute a = ⟦s⟧
  rw [← hs_eq] at hab
  -- hab : ⟦r⟧ ≤ ⟦s⟧ ≡ Reachable bodyGraph r s (definitionally)
  refine ⟨r, rfl, ?_⟩
  constructor
  · -- r →* initial in recGraph: r →*(body) s then s →*(rec) initial
    exact Reachable.trans setup.recGraph
      (Relation.ReflTransGen.mono (fun x y h => Or.inl h) hab)
      hs_mutual.1
  · -- initial →* r in recGraph: lift body path
    exact Relation.ReflTransGen.mono (fun x y h => Or.inl h)
      (setup.initial_reaches_all r)

/-- Body graph reachability lifts to the recursive graph. -/
theorem body_reachable_lifts (setup : RecursionSetup V) {u v : V}
    (h : Reachable setup.bodyGraph u v) : Reachable setup.recGraph u v :=
  Relation.ReflTransGen.mono (fun _ _ h => Or.inl h) h

/-- If `u` cannot reach `initial` in the recursive graph, then any recGraph
    path from `u` uses only body edges. -/
theorem reach_body_of_not_reach_initial (setup : RecursionSetup V) {u v : V}
    (h : Reachable setup.recGraph u v)
    (h_not : ¬Reachable setup.recGraph u setup.initial) :
    Reachable setup.bodyGraph u v := by
  induction h with
  | refl => exact Reachable.refl _ _
  | tail rest step ih =>
    -- rest : ReflTransGen recGraph.edge u b, step : recGraph.edge b v
    cases step with
    | inl body_edge =>
      exact Reachable.trans _ ih (Reachable.single _ body_edge)
    | inr back =>
      obtain ⟨hb_mem, hc_eq⟩ := back
      subst hc_eq
      exfalso
      exact h_not (Reachable.trans _
        (body_reachable_lifts setup ih)
        (Reachable.single _ (Or.inr ⟨hb_mem, rfl⟩)))

/-- If two vertices are mutually reachable in recGraph and neither can reach
    initial, then they are mutually reachable in bodyGraph. -/
theorem non_absorbed_body_mutual (setup : RecursionSetup V) {u v : V}
    (h : MutuallyReachable setup.recGraph u v)
    (h_not : ¬Reachable setup.recGraph u setup.initial) :
    MutuallyReachable setup.bodyGraph u v := by
  have hv_not : ¬Reachable setup.recGraph v setup.initial := by
    intro hv; exact h_not (Reachable.trans _ h.1 hv)
  exact ⟨reach_body_of_not_reach_initial setup h.1 h_not,
         reach_body_of_not_reach_initial setup h.2 hv_not⟩

/-- If vertex `v` is absorbed (mutually reachable with initial in recGraph),
    then `[v]_body ∈ absorbedSet`. -/
theorem absorbed_mem (setup : RecursionSetup V) {v : V}
    (hv : MutuallyReachable setup.recGraph v setup.initial) :
    (⟦v⟧ : SCCQuotient setup.bodyGraph) ∈ setup.absorbedSet :=
  ⟨v, rfl, hv⟩

/-- If vertex `v` is NOT absorbed, then `[v]_body ∉ absorbedSet`. -/
theorem not_absorbed_not_mem (setup : RecursionSetup V) {v : V}
    (hv : ¬MutuallyReachable setup.recGraph v setup.initial) :
    (⟦v⟧ : SCCQuotient setup.bodyGraph) ∉ setup.absorbedSet := by
  intro ⟨w, hw_eq, hw_mutual⟩
  apply hv
  -- w is mutually reachable with initial, and ⟦w⟧ = ⟦v⟧ in body
  -- So MutuallyReachable bodyGraph w v, lift to recGraph
  have hmr : MutuallyReachable setup.bodyGraph w v := by
    have : (⟦w⟧ : SCCQuotient setup.bodyGraph) = ⟦v⟧ := hw_eq
    exact Quotient.exact this
  exact MutuallyReachable.trans _ (MutuallyReachable.symm _
    ⟨body_reachable_lifts setup hmr.1, body_reachable_lifts setup hmr.2⟩) hw_mutual

/-- The forward map φ: vertices to L' absorbedSet, at the vertex level.
    Absorbed vertices map to bot', others to surv [v]_body. -/
private def phi_vertex (setup : RecursionSetup V) (v : V) :
    BottomAbsorption.L' setup.absorbedSet :=
  if h : MutuallyReachable setup.recGraph v setup.initial then
    .bot'
  else
    .surv ⟦v⟧ (not_absorbed_not_mem setup h)

/-- phi_vertex respects recGraph SCC equivalence. -/
private theorem phi_vertex_wd (setup : RecursionSetup V) {u v : V}
    (h : MutuallyReachable setup.recGraph u v) :
    phi_vertex setup u = phi_vertex setup v := by
  simp only [phi_vertex]
  split
  · -- u absorbed
    rename_i hu
    split
    · rfl  -- both absorbed → both bot'
    · -- v not absorbed but u is → contradiction (transitivity)
      rename_i hv
      exact absurd (MutuallyReachable.trans _ (MutuallyReachable.symm _ h) hu) hv
  · -- u not absorbed
    rename_i hu
    split
    · -- v absorbed but u is not → contradiction
      rename_i hv
      exact absurd (MutuallyReachable.trans _ h hv) hu
    · -- neither absorbed → same body SCC class
      rename_i hv
      have hbody := non_absorbed_body_mutual setup h (by
        intro hreach; exact hu ⟨hreach, body_reachable_lifts setup (setup.initial_reaches_all u)⟩)
      congr 1
      exact Quotient.sound hbody

/-- The forward map φ lifted to the recGraph SCC quotient. -/
private def phi (setup : RecursionSetup V) :
    SCCQuotient setup.recGraph → BottomAbsorption.L' setup.absorbedSet :=
  Quotient.lift (phi_vertex setup) (fun u v h => phi_vertex_wd setup h)

/-- The backward map: bodyToRec lifts body quotient elements to rec quotient. -/
private def bodyToRec (setup : RecursionSetup V) :
    SCCQuotient setup.bodyGraph → SCCQuotient setup.recGraph :=
  Quotient.lift (fun v => (⟦v⟧ : SCCQuotient setup.recGraph))
    (fun u v h => Quotient.sound
      ⟨body_reachable_lifts setup h.1, body_reachable_lifts setup h.2⟩)

/-- The backward map ψ: L' absorbedSet → SCCQuotient recGraph. -/
private def psi (setup : RecursionSetup V) :
    BottomAbsorption.L' setup.absorbedSet → SCCQuotient setup.recGraph
  | .bot' => ⟦setup.initial⟧
  | .surv q _ => bodyToRec setup q

/-- φ ∘ ψ = id -/
private theorem phi_psi (setup : RecursionSetup V) (x : BottomAbsorption.L' setup.absorbedSet) :
    phi setup (psi setup x) = x := by
  cases x with
  | bot' =>
    simp only [psi, phi, Quotient.lift_mk, phi_vertex]
    split
    · rfl
    · rename_i h; exact absurd (MutuallyReachable.refl _ _) h
  | surv q hq =>
    simp only [psi, phi, bodyToRec]
    induction q using Quotient.ind with
    | _ v =>
      simp only [Quotient.lift_mk, phi_vertex]
      split
      · rename_i habs
        exact absurd (absorbed_mem setup habs) hq
      · rfl

/-- ψ ∘ φ = id -/
private theorem psi_phi (setup : RecursionSetup V) (x : SCCQuotient setup.recGraph) :
    psi setup (phi setup x) = x := by
  induction x using Quotient.ind with
  | _ v =>
    simp only [phi, Quotient.lift_mk, phi_vertex]
    split
    · -- v absorbed: φ(v) = bot', ψ(bot') = ⟦initial⟧_rec
      -- Need: ⟦initial⟧_rec = ⟦v⟧_rec, i.e., MutuallyReachable recGraph initial v
      rename_i habs
      exact Quotient.sound (MutuallyReachable.symm _ habs)
    · -- v not absorbed: φ(v) = surv ⟦v⟧_body, ψ(surv ⟦v⟧_body) = bodyToRec ⟦v⟧_body = ⟦v⟧_rec
      simp only [psi, bodyToRec, Quotient.lift_mk]

/-- φ is a bijection. -/
private theorem phi_bijective (setup : RecursionSetup V) :
    Function.Bijective (phi setup) :=
  ⟨Function.LeftInverse.injective (psi_phi setup),
   Function.RightInverse.surjective (phi_psi setup)⟩

/-- The lattice ordering on the body quotient agrees with the global
    reachability ordering, lifted to all quotient elements. -/
private theorem body_lattice_le_eq_global (setup : RecursionSetup V)
    (a b : SCCQuotient setup.bodyGraph) :
    @LE.le _ (setup.bodyLattice.toSemilatticeInf.toPartialOrder.toPreorder.toLE) a b ↔ a ≤ b := by
  induction a using Quotient.ind with | _ u =>
  induction b using Quotient.ind with | _ v =>
  exact (setup.body_le_iff_reach u v).trans Iff.rfl

/-- **Recursion Lemma** (Lemma 6).

    If the SCC quotient of the body's state space is a bounded lattice, then
    the SCC quotient of the recursive type's state space also admits a
    bounded lattice structure.

    The proof reduces to the Bottom Absorption Lemma by showing that the set of
    classes absorbed into the initial state is downward-closed and contains ⊥.
    An order isomorphism φ between SCCQuotient(recGraph) and L'(absorbedSet)
    transfers the lattice structure. -/
theorem recursion_preserves_lattice (setup : RecursionSetup V) :
    ∃ (_ : Lattice (SCCQuotient setup.recGraph))
      (_ : OrderBot (SCCQuotient setup.recGraph))
      (_ : OrderTop (SCCQuotient setup.recGraph)), True := by
  -- Case split: either all vertices are absorbed or not
  by_cases h_all : ∀ v : V, MutuallyReachable setup.recGraph v setup.initial
  · -- Case A: All absorbed → singleton quotient → trivial lattice
    have hsub : ∀ a b : SCCQuotient setup.recGraph, a = b := by
      intro a b
      induction a using Quotient.ind with | _ u =>
      induction b using Quotient.ind with | _ v =>
      exact Quotient.sound
        ⟨Reachable.trans _ (h_all u).1 (h_all v).2,
         Reachable.trans _ (h_all v).1 (h_all u).2⟩
    let e : SCCQuotient setup.recGraph := ⟦setup.initial⟧
    refine ⟨?_, ?_, ?_, trivial⟩
    · exact
        { sup := fun a _ => a
          inf := fun a _ => a
          le_sup_left := fun _ _ => le_refl _
          le_sup_right := fun a b => by rw [hsub b a]
          sup_le := fun _ _ _ h _ => h
          inf_le_left := fun _ _ => le_refl _
          inf_le_right := fun a b => by rw [hsub a b]
          le_inf := fun _ _ _ h _ => h }
    · exact { bot := e, bot_le := fun a => by rw [hsub e a] }
    · exact { top := e, le_top := fun a => by rw [hsub a e] }
  · -- Case B: Some vertex not absorbed → apply Bottom Absorption
    push_neg at h_all
    obtain ⟨v₀, hv₀⟩ := h_all
    -- ⊤ ∉ absorbedSet
    have htop_not : @Top.top _ setup.bodyOrderTop.toTop ∉ setup.absorbedSet := by
      intro htop
      exact not_absorbed_not_mem setup hv₀
        (setup.absorbed_lower_closed (setup.bodyOrderTop.le_top _) htop)
    -- Save LE conversion before installing local instances
    have le_conv : ∀ a b : SCCQuotient setup.bodyGraph,
        @LE.le _ setup.bodyLattice.toSemilatticeInf.toPartialOrder.toPreorder.toLE a b ↔
        @LE.le _ (SCCQuotient.instLE setup.bodyGraph) a b :=
      body_lattice_le_eq_global setup
    -- Override ordering hierarchy to use bodyLattice (letI for transparency)
    letI : LE (SCCQuotient setup.bodyGraph) :=
      setup.bodyLattice.toSemilatticeInf.toPartialOrder.toPreorder.toLE
    letI : Preorder (SCCQuotient setup.bodyGraph) :=
      setup.bodyLattice.toSemilatticeInf.toPartialOrder.toPreorder
    letI : PartialOrder (SCCQuotient setup.bodyGraph) :=
      setup.bodyLattice.toSemilatticeInf.toPartialOrder
    letI : Lattice (SCCQuotient setup.bodyGraph) := setup.bodyLattice
    letI : BoundedOrder (SCCQuotient setup.bodyGraph) :=
      { bot := @Bot.bot _ setup.bodyOrderBot.toBot
        bot_le := fun a => (le_conv _ a).mpr (setup.bodyOrderBot.bot_le a)
        top := @Top.top _ setup.bodyOrderTop.toTop
        le_top := fun a => (le_conv a _).mpr (setup.bodyOrderTop.le_top a) }
    -- DownwardClosedBot w.r.t. bodyLattice (now the default)
    have hdc : BottomAbsorption.DownwardClosedBot setup.absorbedSet := by
      refine ⟨setup.bot_mem_absorbed, ?_, htop_not⟩
      intro a b hab ha
      exact setup.absorbed_lower_closed ((le_conv b a).mp hab) ha
    -- Get L' lattice structure from Bottom Absorption
    let lat_L' := BottomAbsorption.L'.mkLattice hdc
    let top_L' := BottomAbsorption.L'.mkOrderTop hdc
    -- ψ preserves order (L' → SCCQuotient recGraph)
    have psi_mono : ∀ x y : BottomAbsorption.L' setup.absorbedSet,
        @LE.le _ lat_L'.toPartialOrder.toPreorder.toLE x y →
        @LE.le _ (SCCQuotient.instLE setup.recGraph)
          (psi setup x) (psi setup y) := by
      intro x y hxy
      cases x with
      | bot' =>
        cases y with
        | bot' => exact Reachable.refl _ _
        | surv q _ =>
          simp only [psi, bodyToRec]
          induction q using Quotient.ind with | _ w =>
          simp only [Quotient.lift_mk]
          exact body_reachable_lifts setup (setup.initial_reaches_all w)
      | surv a ha =>
        cases y with
        | bot' =>
          exfalso
          exact absurd hxy (BottomAbsorption.L'.surv_not_le_bot' a ha)
        | surv b _ =>
          simp only [psi, bodyToRec]
          revert hxy
          induction a using Quotient.ind with | _ u =>
          induction b using Quotient.ind with | _ w =>
          intro hxy
          simp only [Quotient.lift_mk]
          exact body_reachable_lifts setup
            ((setup.body_le_iff_reach u w).mp hxy)
    -- φ preserves order (SCCQuotient recGraph → L')
    have phi_mono : ∀ a b : SCCQuotient setup.recGraph,
        @LE.le _ (SCCQuotient.instLE setup.recGraph) a b →
        @LE.le _ lat_L'.toPartialOrder.toPreorder.toLE
          (phi setup a) (phi setup b) := by
      intro a b hab
      induction a using Quotient.ind with | _ u =>
      induction b using Quotient.ind with | _ v =>
      simp only [phi, Quotient.lift_mk, phi_vertex]
      split
      · trivial  -- u absorbed: bot' ≤ anything
      · rename_i hu
        split
        · -- v absorbed but not u: contradiction
          rename_i hv; exfalso; apply hu
          exact ⟨Reachable.trans _ hab hv.1,
                 body_reachable_lifts setup (setup.initial_reaches_all u)⟩
        · -- Neither absorbed: surv ⟦u⟧ ≤ surv ⟦v⟧
          rename_i hv
          show @LE.le _ setup.bodyLattice.toSemilatticeInf.toPartialOrder.toPreorder.toLE
            ⟦u⟧ ⟦v⟧
          exact (setup.body_le_iff_reach u v).mpr
            (reach_body_of_not_reach_initial setup hab (fun h =>
              hu ⟨h, body_reachable_lifts setup (setup.initial_reaches_all u)⟩))
    -- Define sup/inf via φ/ψ transfer
    let sup' := fun a b => psi setup (lat_L'.toSemilatticeSup.sup (phi setup a) (phi setup b))
    let inf' := fun a b => psi setup (lat_L'.toSemilatticeInf.inf (phi setup a) (phi setup b))
    refine ⟨?_, ?_, ?_, trivial⟩
    · -- Lattice (transfer via φ/ψ round-trip)
      exact
        { sup := sup'
          inf := inf'
          le_sup_left := fun a b => by
            show @LE.le _ (SCCQuotient.instLE _) a (sup' a b)
            have := psi_mono _ _ (@le_sup_left _ lat_L'.toSemilatticeSup (phi setup a) (phi setup b))
            rwa [psi_phi] at this
          le_sup_right := fun a b => by
            show @LE.le _ (SCCQuotient.instLE _) b (sup' a b)
            have := psi_mono _ _ (@le_sup_right _ lat_L'.toSemilatticeSup (phi setup a) (phi setup b))
            rwa [psi_phi] at this
          sup_le := fun a b c h1 h2 => by
            show @LE.le _ (SCCQuotient.instLE _) (sup' a b) c
            have := psi_mono _ _ (@sup_le _ lat_L'.toSemilatticeSup _ _ (phi setup c)
              (phi_mono _ _ h1) (phi_mono _ _ h2))
            rwa [psi_phi] at this
          inf_le_left := fun a b => by
            show @LE.le _ (SCCQuotient.instLE _) (inf' a b) a
            have := psi_mono _ _ (@inf_le_left _ lat_L'.toSemilatticeInf (phi setup a) (phi setup b))
            rwa [psi_phi] at this
          inf_le_right := fun a b => by
            show @LE.le _ (SCCQuotient.instLE _) (inf' a b) b
            have := psi_mono _ _ (@inf_le_right _ lat_L'.toSemilatticeInf (phi setup a) (phi setup b))
            rwa [psi_phi] at this
          le_inf := fun a b c h1 h2 => by
            show @LE.le _ (SCCQuotient.instLE _) a (inf' b c)
            have := psi_mono _ _ (@le_inf _ lat_L'.toSemilatticeInf (phi setup a) _ _
              (phi_mono _ _ h1) (phi_mono _ _ h2))
            rwa [psi_phi] at this }
    · -- OrderBot: ⟦initial⟧ is ⊥ (reaches everything)
      exact
        { bot := ⟦setup.initial⟧
          bot_le := fun a => by
            show @LE.le _ (SCCQuotient.instLE _) ⟦setup.initial⟧ a
            induction a using Quotient.ind with | _ v =>
            exact body_reachable_lifts setup (setup.initial_reaches_all v) }
    · -- OrderTop: psi(⊤_L') = bodyToRec(⊤_body)
      exact
        { top := psi setup (@Top.top _ top_L'.toTop)
          le_top := fun a => by
            show @LE.le _ (SCCQuotient.instLE _) a (psi setup (@Top.top _ top_L'.toTop))
            have := psi_mono _ _ (@le_top _ _ top_L' (phi setup a))
            rwa [psi_phi] at this }

end Reticulate

end
