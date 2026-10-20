/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise315
import DomainTheory.Neighborhood.FunctionSpace
import DomainTheory.Neighborhood.Exercise323.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} (V : NeighborhoodSystem α)
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}





theorem toUnit_unique (f : ApproximableMap V unitSys) : f = toUnit V := Subsingleton.elim _ _

end DomainTheory.Neighborhood
