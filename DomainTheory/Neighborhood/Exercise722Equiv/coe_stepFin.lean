/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise722Decide
import DomainTheory.Neighborhood.Exercise722Equiv.Basic
import DomainTheory.Neighborhood.Exercise722Equiv.coe_stepFinSingle


namespace DomainTheory.Neighborhood

namespace Exercise722

open scoped Computability
open Sum Set







theorem coe_stepFin (e : SExpr) (S : Finset (autState e)) (c : Bool) :
    (↑(stepFin e S c) : Set (autState e)) = (toNFA e).stepSet ↑S c := by
  ext x
  rw [Finset.mem_coe]
  unfold stepFin
  rw [Finset.mem_biUnion, NFA.mem_stepSet]
  constructor
  · rintro ⟨s, hs, hx⟩
    exact ⟨s, hs, by rw [← coe_stepFinSingle e s c]; exact Finset.mem_coe.mpr hx⟩
  · rintro ⟨s, hs, hx⟩
    exact ⟨s, hs, by rw [← coe_stepFinSingle e s c] at hx; exact Finset.mem_coe.mp hx⟩

end Exercise722
end DomainTheory.Neighborhood
