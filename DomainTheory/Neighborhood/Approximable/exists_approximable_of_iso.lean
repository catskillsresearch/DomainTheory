/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import Mathlib.Tactic.Set
import DomainTheory.Neighborhood.Approximable.Basic
import DomainTheory.Neighborhood.Approximable.toElementMap_ofIso


namespace DomainTheory.Neighborhood

open NeighborhoodSystem

variable {α β γ δ : Type*}



namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}













/-- **Theorem 2.7 (statement) (Scott 1981, PRG-19).** "Every isomorphism between domains results from
an approximable mapping." For any domain isomorphism `e`, there is an approximable mapping whose
elementwise action is exactly `e`. -/
theorem exists_approximable_of_iso (e : V₀.Element ≃o V₁.Element) :
    ∃ f : ApproximableMap V₀ V₁, ∀ x, f.toElementMap x = e x :=
  ⟨ofIso e, toElementMap_ofIso e⟩

end ApproximableMap
end DomainTheory.Neighborhood
