/-
Copyright (c) 2026 Alexandre Zua Caldeira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexandre Zua Caldeira
-/

import Reticulate.Spec.Core.SessionType

/-!
# Termination check for recursive session types

Decides syntactically whether a session type contains a "trap"
recursion — a `μX.body` whose every branch loops back to `X` and
never reaches `end_`. The terminology is the paper's: this is the
**Termination** clause of `def:wellformed`. Without it, the lattice
would be missing its bottom element on at least one parallel branch
(see `cor:wfpar` and `ex:wfpar` for the canonical witness).

What is exported.
* `hasExitPath S forbidden` — Boolean: "starting from `S`, there is
  a syntactic path to `end_` that does not pass through an
  occurrence of `var forbidden`."
* `HasExitPath` — `Prop`-valued wrapper for use in statements.
* `isTerminating S` — predicate: every `μX.body` subterm of `S` has
  an exit path avoiding `X`.

Worked examples (pinned as `example`s at the bottom of this file):
* `isTerminating end_` is true.
* `isTerminating (rec_ "X" (var "X"))` is false: every "path" loops
  back to `X` immediately.
* `isTerminating (rec_ "X" (branch [("a", var "X")]))` is false:
  the only branch arm loops.
* `isTerminating (rec_ "X" (branch [("a", var "X"), ("done", end_)]))`
  is true: the `done` arm offers an exit avoiding `X`.

Why the project needs this. The paper proves
`thm:reticulate` (the Reticulate Theorem) under the well-formedness
hypothesis; without termination the bottom element of the SCC
lattice fails to exist. `WFParSufficiency.termination_tightness`
concretises the necessity with the witness `&{a:end, b:μX.&{a:X}}`
recorded as `T_bad`.

Conceptual dependencies.
* `Reticulate.Spec.SessionType` for the AST.

Correspondence with the Python reference. This file is a faithful
port of `reticulate/reticulate/termination.py` lines 182–209:

| Python (`termination.py`)                  | Lean (this file)                          |
|--------------------------------------------|-------------------------------------------|
| `_has_exit_path(node, forbidden)`          | `hasExitPath node forbidden`              |
| `_collect_non_terminating(S)`              | `¬ isTerminating S` witnesses             |
| `is_terminating(S)`                        | `isTerminating S`                         |

The only departure is mechanical: Lean uses inner `where` helpers
so the structural-recursion checker accepts the list traversals.
-/

namespace Reticulate.Spec

namespace SessionType

/-!
### `hasExitPath` — does this subtree escape without hitting `forbidden`?

We return `Bool`: Python's `_has_exit_path` is decidable, and we keep the
Lean version decidable too. A `Prop`-valued wrapper is exposed as
`HasExitPath` below.
-/

/-- `hasExitPath S forbidden` returns `true` exactly when there is
a syntactic path from `S` to `end_` that does not pass through an
occurrence of `var forbidden`.

The recursion is literal: `branch`/`select` need at least one child
to have an exit (`anyPairList`), `par` needs all children to have
an exit (`allList`), `rec_ X body` recurses into `body` with the
same `forbidden` (no shadowing — this matches the Python reference),
`var X` returns `true` iff `X ≠ forbidden`, and `end_` returns
`true` unconditionally.

Used inside `isTerminatingBool` to test, at every `μX.body` node,
that `body` has an exit path avoiding `X`.

Tiny example: `hasExitPath (var "X") "X" = false`,
`hasExitPath (var "X") "Y" = true`. -/
def hasExitPath : SessionType → String → Bool
  | .end_,        _         => true
  | .var X,       forbidden => !(decide (X = forbidden))
  | .branch ms,   forbidden => anyPairList ms forbidden
  | .select ls,   forbidden => anyPairList ls forbidden
  | .par ss,      forbidden => allList ss forbidden
  | .rec_ _ body, forbidden => hasExitPath body forbidden
where
  anyPairList : List (String × SessionType) → String → Bool
    | [],      _         => false
    | p :: tl, forbidden => hasExitPath p.2 forbidden || anyPairList tl forbidden
  allList : List SessionType → String → Bool
    | [],      _         => true
    | s :: tl, forbidden => hasExitPath s forbidden && allList tl forbidden

/-- `Prop`-valued shadow of `hasExitPath`. Convenient when stating
lemmas, since `Bool = true` and `Prop` mix awkwardly under `simp`.
Decidability follows trivially from `hasExitPath` being a function
into `Bool`. -/
def HasExitPath (S : SessionType) (forbidden : String) : Prop :=
  hasExitPath S forbidden = true

/-- Decidability of `HasExitPath`: inherits from the `Bool`-valued
`hasExitPath`. -/
instance (S : SessionType) (forbidden : String) : Decidable (HasExitPath S forbidden) := by
  unfold HasExitPath
  exact inferInstance

/-!
### `isTerminating` — every `rec_` has an exit path

A session type is terminating iff every `μX.body` subterm satisfies
`hasExitPath body X`. We walk the whole AST collecting the check.
-/

/-- The Boolean termination check: returns `true` exactly when
every `rec_ X body` subterm of `S` satisfies `hasExitPath body X`.

A failure anywhere — even buried under a `branch` or `par` — causes
the whole answer to be `false`. So `isTerminatingBool` walks the
entire AST and conjoins the local-`rec_` check with the recursion
into children.

Used to define `isTerminating` and consequently the Termination
clause of `WellFormed`. -/
def isTerminatingBool : SessionType → Bool
  | .end_        => true
  | .var _       => true
  | .branch ms   => allTermPairList ms
  | .select ls   => allTermPairList ls
  | .par ss      => allTermList ss
  | .rec_ X body => hasExitPath body X && isTerminatingBool body
where
  allTermPairList : List (String × SessionType) → Bool
    | []      => true
    | p :: tl => isTerminatingBool p.2 && allTermPairList tl
  allTermList : List SessionType → Bool
    | []      => true
    | s :: tl => isTerminatingBool s && allTermList tl

/-- `Prop`-valued termination predicate, the form used in
`WellFormed` and in paper-aligned theorem statements.

A `SessionType` `S` is *terminating* (in the paper's sense, the
Termination clause of `def:wellformed`) when every recursion
inside it has at least one exit branch that escapes the rec-binder
without going through the binder's variable. The canonical
non-example is `μX.&{a:X}`. -/
def isTerminating (S : SessionType) : Prop := isTerminatingBool S = true

/-- Decidability of `isTerminating`: powers `decide` on small
witness terms. -/
instance (S : SessionType) : Decidable (isTerminating S) := by
  unfold isTerminating
  exact inferInstance

/-! ### Sanity examples from the paper -/

/-- `end_` is trivially terminating. -/
example : isTerminating (.end_ : SessionType) := by decide

/-- `μX.&{a:X,done:end}` is terminating (Reticulate Theorem witness). -/
example : isTerminating
    (.rec_ "X" (.branch [("a", .var "X"), ("done", .end_)])) := by decide

/-- `μX.&{a:X}` is NOT terminating — every arm loops. -/
example : ¬ isTerminating (.rec_ "X" (.branch [("a", .var "X")])) := by decide

/-- Termination is *pointwise* at each `rec_`: outer good + inner bad ⇒ not terminating. -/
example : ¬ isTerminating
    (.branch [("a", .end_),
              ("b", .rec_ "X" (.branch [("a", .var "X")]))]) := by decide

end SessionType

end Reticulate.Spec
