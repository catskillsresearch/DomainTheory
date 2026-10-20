/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Definition83
import DomainTheory.Neighborhood.ApproximableExercises
import DomainTheory.Neighborhood.Theorem85.Basic
import DomainTheory.Neighborhood.Theorem85.principal_compact


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}




section Algebraic

variable {γ : Type u} {V : NeighborhoodSystem γ}






theorem principal_isCompactElt {X : Set γ} (hX : V.mem X) : IsCompactElt (V.principal hX) :=
  fun d hdir h => principal_compact hX d hdir h

end Algebraic
end DomainTheory.Neighborhood
