/-
Copyright (c) 2026 Alexandre Zua Caldeira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexandre Zua Caldeira
-/

/-!
# Session-type abstract syntax

This module defines `SessionType`, the abstract syntax tree (AST) of
the session-type language used throughout the ICE 2026 paper.
It is the data structure on which everything else in
`Reticulate.Spec.*` operates: state-space construction, lattice
analysis, duality, and subtyping all start from a `SessionType`
value.

What is exported.
* `SessionType` — the inductive type with six constructors
  (`end_`, `branch`, `select`, `par`, `rec_`, `var`) matching the
  paper's grammar one-to-one.
* `SessionType.beq` and `beq_iff_eq` — boolean structural equality
  and its correctness proof.
* `DecidableEq SessionType` — built from `beq`; this is what lets
  later files use `decide` to check concrete equalities.

The grammar mirrored exactly is the one in §2 of the paper:

```
S  ::=  end
     |  &{ m₁:S₁ , … , mₙ:Sₙ }         -- branch, n ≥ 0
     |  +{ l₁:S₁ , … , lₙ:Sₙ }         -- selection, n ≥ 0
     |  S₁ ∥ … ∥ Sₙ                    -- n-ary parallel, n ≥ 2
     |  μX.S                            -- recursion
     |  X                               -- recursion variable
```

Why a fresh inductive (rather than reusing `Reticulate.SessionType`).
The legacy `Reticulate.SessionType` carries extra `chain`/`seq`
constructors locked by the modularity campaign (2026-04-11 charter)
and restricts `par` to two children. The paper's grammar is n-ary;
faithfully mechanising it requires `par : List SessionType →
SessionType`. We therefore put the paper-faithful inductive in the
`Reticulate.Spec` namespace, leaving the legacy inductive for older
proofs that have not yet migrated.

Conceptual dependencies.
* None at the type level — this is a freestanding AST. `String` is
  used for branch labels, selection labels, and recursion-variable
  names.

## Design notes

*Inner-`where` helpers.* Lean's structural recursion checker accepts
recursive functions on `SessionType` that descend into list-shaped
children only when the list traversal is exposed via inner `where`
clauses. We use that pattern uniformly: `beq`, `freeVars`,
`stateCount`, etc.

*Decidable equality is hand-built.* `deriving DecidableEq` does not
work on the pair-list constructors. Instead we define a boolean
equality `beq` mutually with its list/pair-list helpers, prove it
reflexive (`beq_refl`) and complete (`beq_sound`), and convert via
`decidable_of_iff`.
-/

namespace Reticulate.Spec

/-- The paper-faithful session-type AST.

A value of this type represents a single session-type expression `S`
from the ICE 2026 grammar. The six constructors and their intended
meaning:

* `end_` — the terminated session: no further methods are available.
* `branch ms` — external choice. The other party picks a method
  label `m` from the list `ms`, after which the session continues
  with the matching child. The label list may be empty
  (`branch [] = &{}`), representing "no methods on offer."
* `select ls` — internal choice (dually): we pick a label and the
  session continues with the matching child. The list may also be
  empty.
* `par ss` — n-ary parallel. The session runs all elements of `ss`
  concurrently and finishes only once all sub-sessions have
  finished.
* `rec_ X body` — recursion: `μX.body`, where `X` may appear free
  inside `body` to refer back to the whole expression.
* `var X` — recursion variable: a bound occurrence of the name `X`
  introduced by some enclosing `rec_ X _`.

Used by every `Reticulate.Spec.*` definition. The constructors are
exhaustive — no syntactic sugar like `chain`/`seq` is encoded here;
those are kept in the legacy `Reticulate.SessionType`. -/
inductive SessionType : Type where
  | end_   : SessionType
  | branch : List (String × SessionType) → SessionType
  | select : List (String × SessionType) → SessionType
  | par    : List SessionType → SessionType
  | rec_   : String → SessionType → SessionType
  | var    : String → SessionType
  deriving Inhabited

namespace SessionType

/-!
### Boolean structural equality

We define `beq` as a structurally recursive function whose list children
are traversed by inner `where` helpers. Lean accepts this through the
auto-generated structural recursion checker.
-/

/-- Boolean structural equality on `SessionType`.

Returns `true` exactly when its two arguments are the same expression
under the obvious "same constructor, same arguments" reading. Used
to build the `DecidableEq` instance below; never relied on directly
by client code.

Implemented as a structurally-recursive function with two inner
helpers (`beqList` for `par`, `beqPairList` for `branch` and
`select`) so that Lean's structural-recursion checker accepts the
list traversal. Correctness is the pair `beq_refl` + `beq_sound`,
packaged as `beq_iff_eq` below. -/
def beq : SessionType → SessionType → Bool
  | .end_,         .end_         => true
  | .branch ms₁,   .branch ms₂   => beqPairList ms₁ ms₂
  | .select ls₁,   .select ls₂   => beqPairList ls₁ ls₂
  | .par ss₁,      .par ss₂      => beqList ss₁ ss₂
  | .rec_ X₁ b₁,   .rec_ X₂ b₂   => (decide (X₁ = X₂)) && beq b₁ b₂
  | .var X₁,       .var X₂       => decide (X₁ = X₂)
  | _,             _             => false
where
  beqList : List SessionType → List SessionType → Bool
    | [],        []        => true
    | a :: as,   b :: bs   => beq a b && beqList as bs
    | _,         _         => false
  beqPairList : List (String × SessionType) → List (String × SessionType) → Bool
    | [],             []             => true
    | (m₁, s₁) :: as, (m₂, s₂) :: bs =>
        (decide (m₁ = m₂)) && beq s₁ s₂ && beqPairList as bs
    | _,              _              => false

/-!
### Reflexivity of `beq`

`beq_refl` says `beq S S = true`. We prove it using a companion
`beq_refl_*` for each list shape. Structural recursion on the list
does the heavy lifting; the outer function recurses on `SessionType`.
-/

/-! Reflexivity of `beq`: every `SessionType` is `beq`-equal to
itself. The "if direction" of `beq_iff_eq`. Proved by structural
induction on `S`, with companion lemmas `beq_refl_list` and
`beq_refl_pairList` handling the list-shaped children. -/

mutual
  /-- Reflexivity of `beq` on `SessionType`: `beq S S = true` for
  every `S`. Proof technique: structural induction on `S`. -/
  theorem beq_refl : ∀ (S : SessionType), beq S S = true
    | .end_ => by simp [beq]
    | .branch ms => by
      simp only [beq]
      exact beq_refl_pairList ms
    | .select ls => by
      simp only [beq]
      exact beq_refl_pairList ls
    | .par ss => by
      simp only [beq]
      exact beq_refl_list ss
    | .rec_ X body => by
      show (decide (X = X) && beq body body) = true
      rw [beq_refl body, decide_eq_true rfl]
      rfl
    | .var _ => by simp [beq]

  /-- `beqList` companion: every list of session types is `beqList`-equal
  to itself. Used inside `beq_refl` to discharge the `par` case. -/
  theorem beq_refl_list : ∀ (ss : List SessionType), beq.beqList ss ss = true
    | [] => by simp [beq.beqList]
    | hd :: tl => by
      simp only [beq.beqList, Bool.and_eq_true]
      exact ⟨beq_refl hd, beq_refl_list tl⟩

  /-- `beqPairList` companion: every list of `(label, sub-type)` pairs is
  `beqPairList`-equal to itself. Used inside `beq_refl` to discharge
  the `branch` and `select` cases. -/
  theorem beq_refl_pairList : ∀ (ms : List (String × SessionType)),
      beq.beqPairList ms ms = true
    | [] => by simp [beq.beqPairList]
    | (m, s) :: tl => by
      show (decide (m = m) && beq s s && beq.beqPairList tl tl) = true
      rw [beq_refl s, beq_refl_pairList tl, decide_eq_true rfl]
      rfl
end

/-!
### Completeness of `beq`

`beq_sound` says `beq S T = true → S = T`. Same mutual-recursion style.
-/

/-! Soundness of `beq`: if `beq S T = true` then `S = T`. The
"only-if direction" of `beq_iff_eq`.

Proved by structural induction on `S` with case analysis on `T`.
Constructor mismatches are dispatched by `simp [beq]` (the matching
clause forces `false`); same-constructor cases use the IH plus the
companion list lemmas. -/

mutual
  /-- Soundness of `beq`: `beq S T = true → S = T`. Proof
  technique: structural induction on `S` with case analysis on
  `T`; mismatched constructors discharge by `simp [beq]`. -/
  theorem beq_sound : ∀ (S T : SessionType), beq S T = true → S = T
    | .end_, T => by
      cases T <;> intro h <;> first | rfl | simp [beq] at h
    | .branch ms, T => by
      cases T with
      | end_       => intro h; simp [beq] at h
      | branch ms' =>
        intro h
        simp only [beq] at h
        exact congrArg _ (beq_sound_pairList ms ms' h)
      | select _   => intro h; simp [beq] at h
      | par _      => intro h; simp [beq] at h
      | rec_ _ _   => intro h; simp [beq] at h
      | var _      => intro h; simp [beq] at h
    | .select ls, T => by
      cases T with
      | end_       => intro h; simp [beq] at h
      | branch _   => intro h; simp [beq] at h
      | select ls' =>
        intro h
        simp only [beq] at h
        exact congrArg _ (beq_sound_pairList ls ls' h)
      | par _      => intro h; simp [beq] at h
      | rec_ _ _   => intro h; simp [beq] at h
      | var _      => intro h; simp [beq] at h
    | .par ss, T => by
      cases T with
      | end_       => intro h; simp [beq] at h
      | branch _   => intro h; simp [beq] at h
      | select _   => intro h; simp [beq] at h
      | par ss'    =>
        intro h
        simp only [beq] at h
        exact congrArg _ (beq_sound_list ss ss' h)
      | rec_ _ _   => intro h; simp [beq] at h
      | var _      => intro h; simp [beq] at h
    | .rec_ X body, T => by
      cases T with
      | end_          => intro h; simp [beq] at h
      | branch _      => intro h; simp [beq] at h
      | select _      => intro h; simp [beq] at h
      | par _         => intro h; simp [beq] at h
      | rec_ X' body' =>
        intro h
        simp only [beq, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨hX, hb⟩ := h
        have := beq_sound body body' hb
        subst hX; subst this; rfl
      | var _         => intro h; simp [beq] at h
    | .var X, T => by
      cases T with
      | end_      => intro h; simp [beq] at h
      | branch _  => intro h; simp [beq] at h
      | select _  => intro h; simp [beq] at h
      | par _     => intro h; simp [beq] at h
      | rec_ _ _  => intro h; simp [beq] at h
      | var X'    =>
        intro h
        simp only [beq, decide_eq_true_eq] at h
        exact congrArg _ h

  /-- `beqList` companion of `beq_sound`: list-shape soundness for
  `par` children. -/
  theorem beq_sound_list : ∀ (ss ss' : List SessionType),
      beq.beqList ss ss' = true → ss = ss'
    | [], [], _ => rfl
    | [], _ :: _, h => by simp [beq.beqList] at h
    | _ :: _, [], h => by simp [beq.beqList] at h
    | hd :: tl, hd' :: tl', h => by
      simp only [beq.beqList, Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      have e1 : hd = hd' := beq_sound hd hd' h1
      have e2 : tl = tl' := beq_sound_list tl tl' h2
      subst e1; subst e2; rfl

  /-- `beqPairList` companion of `beq_sound`: pair-list-shape soundness
  for `branch` and `select` children. -/
  theorem beq_sound_pairList : ∀ (ms ms' : List (String × SessionType)),
      beq.beqPairList ms ms' = true → ms = ms'
    | [], [], _ => rfl
    | [], _ :: _, h => by simp [beq.beqPairList] at h
    | _ :: _, [], h => by simp [beq.beqPairList] at h
    | (m₁, s₁) :: tl, (m₂, s₂) :: tl', h => by
      simp only [beq.beqPairList, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hm, hs⟩, hrest⟩ := h
      have e2 : s₁ = s₂ := beq_sound s₁ s₂ hs
      have e3 : tl = tl' := beq_sound_pairList tl tl' hrest
      subst hm; subst e2; subst e3; rfl
end

/-- `beq` decides structural equality on `SessionType`.

This is the bridge from `Bool`-valued `beq` to `Prop`-valued `=`.
Combines `beq_refl` (one direction) and `beq_sound` (the other) into
the `iff` needed by `decidable_of_iff` below. -/
theorem beq_iff_eq (S T : SessionType) : beq S T = true ↔ S = T :=
  ⟨beq_sound S T, fun h => h ▸ beq_refl S⟩

/-- Decidable equality on `SessionType`: derived from `beq_iff_eq`
via `decidable_of_iff`. This is what allows `decide` to discharge
concrete equalities in downstream `example`s and `simp`-time
rewrites. -/
instance : DecidableEq SessionType := fun S T =>
  decidable_of_iff (beq S T = true) (beq_iff_eq S T)

/-- Smoke test: decidable equality reduces on closed terms. -/
example : ((.end_ : SessionType) = .end_) := by decide

example : ¬ ((.end_ : SessionType) = .var "X") := by decide

example : ((.par [.end_, .var "X"] : SessionType) = .par [.end_, .var "X"]) := by decide

example : ¬ ((.par [.end_, .var "X"] : SessionType) = .par [.end_, .var "Y"]) := by decide

end SessionType

end Reticulate.Spec
