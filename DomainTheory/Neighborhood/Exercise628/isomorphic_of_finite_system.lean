/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Lemma615
import DomainTheory.Neighborhood.Proposition612
import DomainTheory.Neighborhood.Exercise628.Basic
import DomainTheory.Neighborhood.Exercise628.isomorphic_of_trianglelefteq_both
import DomainTheory.Neighborhood.Exercise628.finite_element_of_isFinite


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}







/-- **Exercise 6.28 (Scott 1981, PRG-19; suggested by G. Plotkin).** If `𝒟` and `ℰ` are *finite*
neighbourhood systems with `𝒟 ⊴ ℰ` and `ℰ ⊴ 𝒟`, then `𝒟 ≅ ℰ`. -/
theorem isomorphic_of_finite_system (hD : D.IsFinite) (hE : E.IsFinite)
    (h₁ : D ⊴ E) (h₂ : E ⊴ D) : D ≅ᴰ E := by
  have := finite_element_of_isFinite hD
  have := finite_element_of_isFinite hE
  exact isomorphic_of_trianglelefteq_both h₁ h₂

end DomainTheory.Neighborhood
