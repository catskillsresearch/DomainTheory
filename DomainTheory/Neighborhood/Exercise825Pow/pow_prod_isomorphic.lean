/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise316
import Mathlib.Logic.Equiv.Nat
import DomainTheory.Neighborhood.Exercise825Pow.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem

variable {α : Type*}







/-- **Exercise 8.25 (Scott 1981, PRG-19), first step: `𝒟^∞ × 𝒟^∞ ≅ 𝒟^∞`**, for any `𝒟`. Specialized
to `𝒟 = 𝒰` this is Scott's `𝒰^∞ × 𝒰^∞ ≅ 𝒰^∞`. -/
theorem pow_prod_isomorphic (V : NeighborhoodSystem α) :
    prod (iterSys V) (iterSys V) ≅ᴰ iterSys V :=
  ⟨powProdOrderIso V⟩

end DomainTheory.Neighborhood
