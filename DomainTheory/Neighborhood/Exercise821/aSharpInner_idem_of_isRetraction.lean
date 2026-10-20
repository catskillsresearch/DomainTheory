/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise717Part2
import DomainTheory.Neighborhood.Definition89
import DomainTheory.Neighborhood.Proposition810
import DomainTheory.Neighborhood.Proposition810b
import DomainTheory.Neighborhood.Lemma615
import DomainTheory.Neighborhood.Exercise821.Basic
import DomainTheory.Neighborhood.Exercise821.aSharpInner_eq


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}



variable {hD : ∀ X, D.mem X → X.Nonempty}








variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}












/-- **Exercise 8.21(b)(2).** If `a` is a retraction (`a∘a = a`), so is its recursive extension
`aSharpInner a`: the specialization of `gMap_selfComp_eq_of_isRetraction` to `D := U`. -/
theorem aSharpInner_idem_of_isRetraction {a : ApproximableMap U U} (ha : IsRetraction a) :
    IsRetraction (aSharpInner a) := by
  show (aSharpInner a).comp (aSharpInner a) = aSharpInner a
  rw [aSharpInner_eq]
  exact gMap_selfComp_eq_of_isRetraction ha

end DomainTheory.Neighborhood
