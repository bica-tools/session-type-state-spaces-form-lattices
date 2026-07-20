/-
Copyright (c) 2026 Alexandre Zua Caldeira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexandre Zua Caldeira
-/

import Mathlib.Data.Finset.Basic
import Reticulate.Spec.Core.SessionType

/-!
# Free variables, bound variables, and closedness

When is a session type "closed"? This module gives the precise
answer: a session type is closed when none of its recursion
variables `var X` appear without an enclosing binder
`rec_ X _`. The notion is one of the three clauses of
`def:wellformed` in the paper (the "no dangling references"
clause).

What is exported.
* `freeVars S` — the finite set of recursion-variable names that
  occur unbound in `S`.
* `boundVars S` — the finite set of names that appear as a
  `rec_ X _` binder anywhere inside `S`.
* `closed S` — the predicate `freeVars S = ∅`. Decidable.

Semantics in one line each:
* `freeVars (var X) = {X}` — a bare variable is free.
* `freeVars (rec_ X body) = freeVars body \ {X}` — recursion
  removes its own binder name.
* `freeVars` distributes as a union over the children of `branch`,
  `select`, and `par`.

Worked examples (also recorded as `example` checks at the bottom of
this file):
* `freeVars (var "X") = {"X"}`, so `var "X"` is **not** closed.
* `freeVars (rec_ "X" (var "X")) = ∅`, so `rec_ "X" (var "X")` is
  closed. (Note that this term is closed even though it is *not*
  terminating — closedness and termination are independent
  clauses of well-formedness.)
* `freeVars (rec_ "X" (branch [("a", var "X"), ("done", end_)])) = ∅`,
  so the canonical "loop-or-quit" recursion is closed.

Why we need this module. The state-space construction in
`Reticulate.Spec.StateSpace` lays out states for every sub-term and
routes recursion-variable occurrences to their binder. Free
variables have nowhere to go and would produce dangling edges, so
later well-formedness checks (`Reticulate.Spec.WellFormed.closed`,
`parClosed`) ban them.

Conceptual dependencies.
* `Reticulate.Spec.SessionType` for the AST.
* Mathlib's `Finset String` for set-valued results — `Finset` gives
  computable union/difference and decidable equality, both of which
  we exploit.
-/

namespace Reticulate.Spec

namespace SessionType

open Classical in
/-- The finite set of recursion-variable names that occur free in `S`.

A name `X` is *free* in `S` when at least one occurrence of
`var X` inside `S` is not under an enclosing `rec_ X _` binder. The
set difference `freeVars body \ {X}` in the `rec_` case is what
makes the binder do its work: any free `X` inside `body` is removed,
because the surrounding `rec_ X` provides the binder.

Used by `closed`, by `parClosed` (which checks par-children are
closed), and by all `freeVars`-invariance lemmas in
`Reticulate.Spec.Duality` and `Reticulate.Spec.SubtypingEmbedding`. -/
def freeVars : SessionType → Finset String
  | .end_        => ∅
  | .var X       => {X}
  | .branch ms   => freeVarsPairList ms
  | .select ls   => freeVarsPairList ls
  | .par ss      => freeVarsList ss
  | .rec_ X body => freeVars body \ {X}
where
  freeVarsList : List SessionType → Finset String
    | []      => ∅
    | s :: tl => freeVars s ∪ freeVarsList tl
  freeVarsPairList : List (String × SessionType) → Finset String
    | []      => ∅
    | p :: tl => freeVars p.2 ∪ freeVarsPairList tl

/-- The finite set of recursion-variable names that occur as a
binder anywhere inside `S`.

A name `X` is bound in `S` when there exists a `rec_ X _` node
somewhere in the AST. Note: this is the set of *binder names*, not
the set of *bound occurrences*. A `rec_ X` whose body contains no
`var X` still contributes `X` to `boundVars`.

Currently informational; not consumed elsewhere in `Reticulate.Spec.*`,
but kept for symmetry with `freeVars` and for use in future
substitution-style developments. -/
def boundVars : SessionType → Finset String
  | .end_        => ∅
  | .var _       => ∅
  | .branch ms   => boundVarsPairList ms
  | .select ls   => boundVarsPairList ls
  | .par ss      => boundVarsList ss
  | .rec_ X body => insert X (boundVars body)
where
  boundVarsList : List SessionType → Finset String
    | []      => ∅
    | s :: tl => boundVars s ∪ boundVarsList tl
  boundVarsPairList : List (String × SessionType) → Finset String
    | []      => ∅
    | p :: tl => boundVars p.2 ∪ boundVarsPairList tl

/-- A session type is *closed* when it has no free recursion
variables.

This is one of three clauses of `def:wellformed` in the paper —
specifically the "Closedness" clause: every recursion variable
occurrence must be inside the scope of a corresponding binder.

Worked-tiny-examples:
* `closed end_` is true.
* `closed (var "X")` is false.
* `closed (rec_ "X" (var "X"))` is true.
* `closed (rec_ "X" (var "Y"))` is false: `Y` is not bound.

Used by `Reticulate.Spec.WellFormed.WellFormed` as the second
conjunct, and by `parClosed` as the per-child closedness check at
each `par` node. -/
def closed (S : SessionType) : Prop := freeVars S = ∅

/-- Closedness is decidable: it reduces to a `Finset`-equality check
on the (finite) `freeVars` set. Powers `decide` on the `example`s
below. -/
instance (S : SessionType) : Decidable (closed S) := by
  unfold closed
  exact inferInstance

/-! ### Sanity examples -/

/-- `end_` is closed. -/
example : closed (.end_ : SessionType) := by decide

/-- `var "X"` is not closed. -/
example : ¬ closed ((.var "X") : SessionType) := by decide

/-- `rec_ X (var X)` is closed (the binder absorbs the free var). -/
example : closed (.rec_ "X" (.var "X")) := by decide

/-- A µX.&{a:X,done:end} is closed. -/
example : closed (.rec_ "X"
    (.branch [("a", .var "X"), ("done", .end_)])) := by decide

end SessionType

end Reticulate.Spec
