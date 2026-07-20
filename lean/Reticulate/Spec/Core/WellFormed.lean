/-
Copyright (c) 2026 Alexandre Zua Caldeira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexandre Zua Caldeira
-/

import Reticulate.Spec.Core.FreeVars
import Reticulate.Spec.Core.Termination

/-!
# Well-formedness (the four-clause version)

**AMENDED 2026-05-28 (director-approved α):** `noDupKeys` added as
an additive conjunct of `WellFormed`, codifying the silently-assumed
distinct-labels invariant of the grammar §2.1 and the parsers. The
grammar notation `&{m₁:S₁,…,mₙ:Sₙ}` (and dually `+{l₁:S₁,…,lₙ:Sₙ}`),
the Python `reticulateP` parser's dict semantics, the BICA Java
parser's reject behaviour, and `lem:polarity` all silently assume
distinct labels in each branch / selection node. The previous
three-clause `WellFormed` (terminating ∧ closed ∧ parClosed) did not
codify this assumption; the new `noDupKeys` clause does.

The amendment is **additive**: every previously well-formed (under
three clauses) witness with distinct labels at every choice node
remains well-formed; the only witnesses ruled out are those with
duplicate labels (which were never intended to be in the language).

The paper's well-formedness predicate (`def:wellformed` in §2 of
the ICE 2026 paper) is, post-amendment, a conjunction of four
clauses. This module defines the predicate as it appears
post-amendment and exposes it as `WellFormed`.

The four clauses, written as Lean predicates from prior modules:

* **Closedness** — `closed S` (from `Reticulate.Spec.FreeVars`):
  every `var X` is under a binder.
* **Termination** — `isTerminating S` (from
  `Reticulate.Spec.Termination`): every `μX.body` has an exit path
  avoiding `X`.
* **Par-closedness** — `parClosed S` (defined here): at every
  `par ss` node, every child `sᵢ ∈ ss` has no free recursion
  variables.
* **No duplicate keys** — `noDupKeys S` (defined here, 2026-05-28
  amendment): at every `branch ms` / `select ls` node, the
  method/label names are pairwise distinct.

`WellFormed S` is the conjunction of all four. All four clauses
are decidable; their conjunction is too.

## Why three clauses (and how the paper's text evolved)

The originally submitted paper (commit 471ff8d1) tied
well-formedness to the Termination clause alone. That turned out
insufficient on two fronts:

1. The A47h rebuttal draft (2026-04-20) observed that a type like
   `var "Y"` trivially passes Termination (it contains no
   `rec_`) but obviously is not a sensible session type. The
   `closed` clause rules these out.
2. Audit Finding 4 (2026-04-22) observed that even a closed and
   terminating type can have a `par`-subterm whose individual
   children are not closed, and the product-lattice argument used
   in the Reticulate Theorem (`thm:reticulate`) breaks on such
   types. The witness is `μX.(&{a:X, b:end} ∥ end)`: the outer
   `μX` binds the inner `X`, so the whole term is `closed`, but
   the par-child `&{a:X, b:end}` viewed in isolation has free
   variable `X`. The `parClosed` clause rules these out.

The Python reference enforces (2) operationally — at
`reticulate/reticulate/statespace.py:553` it builds each
par-child's state space with a fresh environment — and the Lean
definition mirrors that by demanding closedness pointwise at every
`par` node.

What is exported.
* `parClosedBool`, `parClosed` — the third clause as a Boolean
  function and a `Prop`.
* `WellFormed` — the three-clause conjunction.
* Witnesses `T_good`, `T_bad`, `T_bad2` for the rebuttal and
  audit-finding examples, with `decide`-checked verdicts.

Conceptual dependencies.
* `Reticulate.Spec.FreeVars` for `freeVars` and `closed`.
* `Reticulate.Spec.Termination` for `isTerminating`.

Downstream consumers.
* `Reticulate.Spec.StateSpaceLattice.reticulate_lattice` takes
  `WellFormed S` as its sole hypothesis.
* `Reticulate.Spec.Duality.dual_WellFormed` proves invariance under
  `dual`.
* `Reticulate.WFParSufficiency.termination_tightness` exhibits a
  type that violates the Termination clause and whose lattice
  conclusion fails — the witness is `T_bad` here, paper
  `ex:wfpar`.
-/

namespace Reticulate.Spec

namespace SessionType

/-!
### `parClosed` — every `par`-child is closed

Every occurrence of `par ss` must compose *closed* sub-protocols: each
`sᵢ ∈ ss` must have `freeVars sᵢ = ∅`. We also recurse into every
sub-term so that nested `par` under branches / selections / recursions
is caught too.

This is Audit Finding 4 (2026-04-22); it matches Python's structural
choice at `statespace.py:553` to build each par-child's state space
with a fresh variable environment.
-/

/-- Boolean version of the par-closedness check.

At every `par ss` subterm, both:
* every child `sᵢ` has empty `freeVars` (`allClosedList`), AND
* the recursion continues into every `sᵢ` (`parClosedList`).

For the other constructors the function simply recurses into
children. This way an offending `par` anywhere in the AST — under
a `branch`, inside a `rec_`, etc. — surfaces as `false`.

Used to define `parClosed`, which is the third conjunct of
`WellFormed`. -/
def parClosedBool : SessionType → Bool
  | .end_        => true
  | .var _       => true
  | .branch ms   => parClosedPairList ms
  | .select ls   => parClosedPairList ls
  | .par ss      => allClosedList ss && parClosedList ss
  | .rec_ _ body => parClosedBool body
where
  /-- Every element of the list has empty `freeVars`. -/
  allClosedList : List SessionType → Bool
    | []      => true
    | s :: tl => decide (freeVars s = ∅) && allClosedList tl
  /-- Recurse `parClosedBool` into every element of the list. -/
  parClosedList : List SessionType → Bool
    | []      => true
    | s :: tl => parClosedBool s && parClosedList tl
  /-- Recurse `parClosedBool` into the second component of every pair. -/
  parClosedPairList : List (String × SessionType) → Bool
    | []      => true
    | p :: tl => parClosedBool p.2 && parClosedPairList tl

/-- `Prop`-valued par-closedness: at every `par` subterm, every
child has empty `freeVars`.

The third conjunct of `WellFormed`. Compositionality of the product
lattice argument — every `par`-child contributes its own factor to
the product `\mathcal{L}(S_1) \times \cdots \times \mathcal{L}(S_n)` — needs
each factor to be a *closed* type. `parClosed` enforces that
everywhere a `par` appears, however deeply nested. -/
def parClosed (S : SessionType) : Prop := parClosedBool S = true

/-- Decidability of par-closedness; powers `decide` on the worked
witnesses. -/
instance (S : SessionType) : Decidable (parClosed S) := by
  unfold parClosed
  exact inferInstance

/-!
### `noDupKeys` — distinct labels at every choice node

**Amended 2026-05-28 (director-approved α).** The grammar §2.1
notation `&{m₁:S₁,…,mₙ:Sₙ}` and the parsers' dict semantics silently
assume distinct labels. This clause codifies that assumption.
Required for `subGH_refl` on branch / select nodes (without
distinct keys, the first-hit lookup in `subGHFuel`'s
`hasKeyCoveredFuel` can miss the intended continuation, and
`subGH_refl` is false on a counter-witness such as
`&{a:end, a:var "X"}`).
-/

/-- Boolean version of the distinct-keys check.

At every `branch ms` / `select ls` subterm:
* the list of keys (`.map Prod.fst`) has no duplicate (`List.Nodup`
  via `decide`); AND
* the function recurses into every continuation `s ∈ ms.map Prod.snd`.

For `par ss`, recurse into every component. For `rec_ X body`,
recurse into `body`. Terminal cases (`end_`, `var X`) are `true`. -/
def noDupKeysBool : SessionType → Bool
  | .end_        => true
  | .var _       => true
  | .branch ms   => (decide ((ms.map Prod.fst).Nodup)) && noDupKeysPairList ms
  | .select ls   => (decide ((ls.map Prod.fst).Nodup)) && noDupKeysPairList ls
  | .par ss      => noDupKeysList ss
  | .rec_ _ body => noDupKeysBool body
where
  /-- Recurse `noDupKeysBool` into every element of the list. -/
  noDupKeysList : List SessionType → Bool
    | []      => true
    | s :: tl => noDupKeysBool s && noDupKeysList tl
  /-- Recurse `noDupKeysBool` into the second component of every
  pair. -/
  noDupKeysPairList : List (String × SessionType) → Bool
    | []      => true
    | p :: tl => noDupKeysBool p.2 && noDupKeysPairList tl

/-- `Prop`-valued no-duplicate-keys-at-every-choice-node: at every
`branch` / `select` subterm, the labels are pairwise distinct.

The fourth conjunct of `WellFormed` (post-2026-05-28 amendment). -/
def noDupKeys (S : SessionType) : Prop := noDupKeysBool S = true

/-- Decidability of `noDupKeys`; powers `decide` on the worked
witnesses. -/
instance (S : SessionType) : Decidable (noDupKeys S) := by
  unfold noDupKeys
  exact inferInstance

/-- **Well-formedness, the four-clause version (paper
`def:wellformed`, 2026-05-28 amendment).**

`WellFormed S` is the conjunction:

* `isTerminating S` — every `μX.body` admits an exit path
  avoiding `X` (rules out `μX.&{a:X}`);
* `closed S` — no free recursion variables anywhere (rules out
  `var "Y"`, `rec_ "X" (var "Y")`);
* `parClosed S` — at every `par` subterm, every child is itself
  closed (rules out `μX.(&{a:X, b:end} ∥ end)`);
* `noDupKeys S` — at every `branch` / `select` subterm, the
  labels are pairwise distinct (rules out `&{a:end, a:var "X"}`,
  per the 2026-05-28 amendment).

This is the precondition of the Reticulate Theorem
(`thm:reticulate`): every well-formed session type's SCC quotient
is a bounded lattice. -/
def WellFormed (S : SessionType) : Prop :=
  isTerminating S ∧ closed S ∧ parClosed S ∧ noDupKeys S

/-- Decidability of `WellFormed`: each conjunct is decidable, so
the conjunction is too. -/
instance (S : SessionType) : Decidable (WellFormed S) := by
  unfold WellFormed
  exact inferInstance

/-!
### Additive `noDupKeys` inversion helpers (2026-05-28b)

Convenience destructors used by `Reticulate.Faithful.fullAbstraction`'s
FA biconditional discharge. Each lemma is a one-line inversion of the
`noDupKeysBool` `Bool` function via `simp [noDupKeysBool, ...]`. They
are purely additive — they add no new substrate, only expose the
boolean conjunctions of `noDupKeysBool` as inversion principles.
-/

/-- Branch labels-distinct inversion. -/
theorem noDupKeys_branch_labels {ms : List (String × SessionType)}
    (h : noDupKeys (.branch ms)) : (ms.map Prod.fst).Nodup := by
  unfold noDupKeys noDupKeysBool at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- Branch continuations-noDupKeys inversion (raw `noDupKeysPairList`
form). -/
theorem noDupKeys_branch_conts {ms : List (String × SessionType)}
    (h : noDupKeys (.branch ms)) :
    noDupKeysBool.noDupKeysPairList ms = true := by
  unfold noDupKeys noDupKeysBool at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-- Select labels-distinct inversion. -/
theorem noDupKeys_select_labels {ls : List (String × SessionType)}
    (h : noDupKeys (.select ls)) : (ls.map Prod.fst).Nodup := by
  unfold noDupKeys noDupKeysBool at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- Select continuations-noDupKeys inversion. -/
theorem noDupKeys_select_conts {ls : List (String × SessionType)}
    (h : noDupKeys (.select ls)) :
    noDupKeysBool.noDupKeysPairList ls = true := by
  unfold noDupKeys noDupKeysBool at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-- Par children-noDupKeys inversion. -/
theorem noDupKeys_par_conts {ss : List SessionType}
    (h : noDupKeys (.par ss)) :
    noDupKeysBool.noDupKeysList ss = true := by
  unfold noDupKeys noDupKeysBool at h
  exact h

/-- Rec body-noDupKeys inversion. -/
theorem noDupKeys_rec_body {X : String} {body : SessionType}
    (h : noDupKeys (.rec_ X body)) : noDupKeys body := by
  unfold noDupKeys noDupKeysBool at h
  exact h

/-- `noDupKeysPairList` cons-head: continuation is `noDupKeys`. -/
theorem noDupKeysPairList_head {p : String × SessionType}
    {tl : List (String × SessionType)}
    (h : noDupKeysBool.noDupKeysPairList (p :: tl) = true) :
    noDupKeys p.2 := by
  simp only [noDupKeysBool.noDupKeysPairList, Bool.and_eq_true] at h
  exact h.1

/-- `noDupKeysPairList` cons-tail. -/
theorem noDupKeysPairList_tail {p : String × SessionType}
    {tl : List (String × SessionType)}
    (h : noDupKeysBool.noDupKeysPairList (p :: tl) = true) :
    noDupKeysBool.noDupKeysPairList tl = true := by
  simp only [noDupKeysBool.noDupKeysPairList, Bool.and_eq_true] at h
  exact h.2

/-- `noDupKeysList` cons-head: child is `noDupKeys`. -/
theorem noDupKeysList_head {s : SessionType} {tl : List SessionType}
    (h : noDupKeysBool.noDupKeysList (s :: tl) = true) :
    noDupKeys s := by
  simp only [noDupKeysBool.noDupKeysList, Bool.and_eq_true] at h
  exact h.1

/-- `noDupKeysList` cons-tail. -/
theorem noDupKeysList_tail {s : SessionType} {tl : List SessionType}
    (h : noDupKeysBool.noDupKeysList (s :: tl) = true) :
    noDupKeysBool.noDupKeysList tl = true := by
  simp only [noDupKeysBool.noDupKeysList, Bool.and_eq_true] at h
  exact h.2

/-- `WellFormed`'s `noDupKeys` projection. -/
theorem noDupKeys_of_WellFormed {S : SessionType} (h : WellFormed S) :
    noDupKeys S := h.2.2.2

/-!
### Worked witnesses for the rebuttal
-/

/-- A canonical well-formed witness: `(μX.&{a:X, done:end}) ∥ &{b:end}`.

Used in the A47h rebuttal as a positive example of a recursive type
under parallel composition — the recursion body `&{a:X, done:end}`
has both a looping arm (`a`) and an exit arm (`done`), and the
parallel sibling `&{b:end}` is closed. All three `WellFormed`
clauses pass; the `decide`-checked `example` immediately below
confirms it. -/
def T_good : SessionType :=
  .par [.rec_ "X" (.branch [("a", .var "X"), ("done", .end_)]),
        .branch [("b", .end_)]]

/-- A canonical ill-formed witness: `&{a:end, b:μX.&{a:X}}`.

Paper `ex:wfpar` (`main.tex` line 912–924). The inner recursion
`μX.&{a:X}` has only a looping arm — no `done` exit — so it fails
the Termination clause. This is the witness whose state space is
mechanised in `Reticulate.Counterexample` (the canonical par-closure
failure witness referenced from `WFParSufficiency`). -/
def T_bad : SessionType :=
  .branch [("a", .end_),
           ("b", .rec_ "X" (.branch [("a", .var "X")]))]

/-- `T_good` is well-formed (terminating, closed, and every `par`-child
is closed). -/
example : WellFormed T_good := by decide

/-- `T_bad` is NOT well-formed (non-terminating `μX.&{a:X}` subterm). -/
example : ¬ WellFormed T_bad := by decide

/-!
### Audit Finding 4 witness (Phase 1b-β2-III)

`T_bad2 ≜ μX.(&{a:X, b:end} ∥ end)` is syntactically *terminating* and
*closed* at the top level (the outer `μX` binds the `X` in the par-child),
yet the par-child `&{a:X, b:end}` has a non-empty `freeVars = {X}`. The
product-lattice compositionality argument requires every par-child to be
a self-contained closed protocol; `parClosed` rejects this witness.
-/

/-- The Audit Finding 4 witness: `μX.(&{a:X, b:end} ∥ end)`.

Top-level `closed` and `isTerminating` both hold (the `b:end` arm
is the exit path; the outer `μX` binds the inner `X`), but the
par-child `&{a:X, b:end}` viewed in isolation has free variable
`X`. So `parClosed` fires and `WellFormed T_bad2` fails — exactly
the case `parClosed` was added to catch. -/
def T_bad2 : SessionType :=
  .rec_ "X" (.par [.branch [("a", .var "X"), ("b", .end_)], .end_])

/-- `parClosed` rejects `T_bad2` — the par-child `&{a:X, b:end}` has a
free `X`, even though the outer `μX` binds it. -/
example : ¬ parClosed T_bad2 := by decide

/-- `T_bad2` is therefore not well-formed. -/
example : ¬ WellFormed T_bad2 := by decide

/-!
### `#eval` cross-checks

Produce verbatim boolean verdicts via the decidable instance.
-/

-- Should print `true`.
#eval decide (WellFormed T_good)

-- Should print `false`.
#eval decide (WellFormed T_bad)

-- Should print `false` (Audit Finding 4).
#eval decide (WellFormed T_bad2)

-- Should print `false` (the specific clause that fires).
#eval decide (parClosed T_bad2)

end SessionType

end Reticulate.Spec
