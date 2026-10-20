/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise315
import DomainTheory.Neighborhood.Exercise316.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem

variable {α : Type*}









variable (V : NeighborhoodSystem α)


variable {V}





























/-- **Exercise 3.16 (Scott 1981, PRG-19).** `𝒟^∞ ≅ 𝒟 × 𝒟^∞`. -/
theorem iter_isomorphic (V : NeighborhoodSystem α) : iterSys V ≅ᴰ prod V (iterSys V) :=
  ⟨iterProdIso V⟩

end DomainTheory.Neighborhood
