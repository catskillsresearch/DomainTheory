/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Example44
import DomainTheory.Neighborhood.Exercise326
import DomainTheory.Neighborhood.Exercise419.Basic


namespace DomainTheory.Neighborhood.Exercise419

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap ExampleB Example44


/-- **Exercise 4.19 — Peano (iii) for `{0,1}*`.** Induction: a predicate holding at `Λ` and closed
under both successors holds everywhere. (This is `List.rec`; it is the two-successor analogue of
Definition 4.5(iii) and the recursion engine behind `tail`/`empty`/`zero`/`one`.) -/
theorem peano_induction (P : Str → Prop) (hnil : P []) (hcons : ∀ b σ, P σ → P (b :: σ)) :
    ∀ σ, P σ := by
  intro σ
  induction σ with
  | nil => exact hnil
  | cons b σ ih => exact hcons b σ ih

end DomainTheory.Neighborhood.Exercise419
