/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise407
import DomainTheory.Neighborhood.Exercise509.Basic
import DomainTheory.Neighborhood.Exercise509.iterElem_le_fixElement
import DomainTheory.Neighborhood.Exercise509.comp_self_iterElem


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- **Exercise 5.9 (Scott 1981, PRG-19).** In particular `fix(f) = fix(f²)`: the `f²`-chain
`f^{2n}(⊥)` is cofinal in the `f`-chain `fⁿ(⊥)`, so the two least fixed points coincide. -/
theorem fixElement_iterTwice (f : ApproximableMap V V) :
    f.fixElement = (f.comp f).fixElement := by
  apply le_antisymm
  · -- `fix f ⊑ fix f²`: `fⁿ⊥ ⊑ f^{2n}⊥ = (f²)ⁿ⊥ ⊑ fix f²`.
    rw [fixElement_eq_iSupDirected f]
    apply NeighborhoodSystem.iSupDirected_le
    intro n
    calc f.iterElem n ≤ f.iterElem (2 * n) := iterElem_mono f (by omega)
      _ = (f.comp f).iterElem n := (comp_self_iterElem f n).symm
      _ ≤ (f.comp f).fixElement := iterElem_le_fixElement (f.comp f) n
  · -- `fix f² ⊑ fix f`: `fix f` is a fixed point of `f²`.
    refine fixElement_le_of_toElementMap_le (f.comp f) (le_of_eq ?_)
    rw [toElementMap_comp, toElementMap_fixElement, toElementMap_fixElement]

end ApproximableMap
end DomainTheory.Neighborhood
