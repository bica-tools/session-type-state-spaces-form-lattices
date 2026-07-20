/-
Copyright (c) 2026 Alexandre Zua Caldeira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexandre Zua Caldeira
-/
import Reticulate.Spec.StateSpace.StateSpaceLattice.ParAndBundles
import Reticulate.Spec.StateSpace.StateSpaceLattice.BranchSelect
import Reticulate.Spec.StateSpace.StateSpaceLattice.Universal

/-!
# Reticulate Theorem (facade)

This file is a **thin facade** preserving the legacy module name
`Reticulate.Spec.StateSpace.StateSpaceLattice` while the actual content
has been split into three sub-modules under
`Reticulate.Spec.StateSpace.StateSpaceLattice/`:

* `ParAndBundles.lean` — Bridge 1 (`end_` subsingleton), Bridge 2
  (BoundedOrder for `par ss` and every session type), Phase 1b-β1c-full
  Steps 1-6 for `par` (stride bijection, edge coordinate change,
  componentwise reachability, MutuallyReachable iff, order isomorphism,
  lattice transport), and the `end_`/`var` `SCCLatticeStruct` bundles.
* `BranchSelect.lean` — Child-index extraction, `branchChildOf` /
  `selectChildOf`, branch/select sup/inf machinery, class-level
  operators, lattice axioms via `Quotient.inductionOn₂`,
  `select_latticeStruct`.
* `Universal.lean` — §F (umbrella theorem): the **universal
  `SCCLatticeStruct` assembly** (`universal_latticeStruct`) — structural
  recursion over `SessionType` under `parClosed` — which is the
  load-bearing piece behind the paper-T1 headline
  `reticulate_theorem`.

External imports / qualified-name citations continue to resolve through
this facade. The split was performed 2026-05-17 as a navigation
improvement (the original file was 9,317 LoC); the namespace
`Reticulate.Spec.SessionType` is preserved across all three sub-files.

See `docs/specs/lean-mechanisation-architecture.md` §7 for the
sub-division rationale.
-/
