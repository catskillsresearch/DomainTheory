/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.funOf_isScottContinuous_left


namespace DomainTheory.DataTypesAsLattices























/-- Appendix calculation: `d(d) = ⋃ { e_l(e_l) | e_l ⊆ d }`. -/
theorem funOf_diag_iUnion (d : Pomega) :
    funOf d d = ⋃ l, {m | e l ⊆ d ∧ m ∈ funOf (e l) (e l)} := by
  have h := theorem_1_3_diag (x := d)
    (f := fun u y => funOf u y)
    (fun y => funOf_isScottContinuous_left y)
    (fun u => funOf_isScottContinuous u)
  exact h

end DomainTheory.DataTypesAsLattices
