/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise619
import DomainTheory.Neighborhood.Definition613
import DomainTheory.Neighborhood.Exercise213
import DomainTheory.Neighborhood.FunctionSpace
import DomainTheory.Neighborhood.Exercise619PartB.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise619
open DomainTheory.Neighborhood.Example62 DomainTheory.Neighborhood.ExampleB
open DomainTheory.Neighborhood.Exercise510

namespace Exercise619





variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}







/-- **`(g₀ ∘ f₀) × (g₁ ∘ f₁) = (g₀ × g₁) ∘ (f₀ × f₁)`.** -/
theorem prodMapTok_comp (f₀ : ApproximableMap A₀.sys B₀.sys) (f₁ : ApproximableMap A₁.sys B₁.sys)
    (g₀ : ApproximableMap B₀.sys C₀.sys) (g₁ : ApproximableMap B₁.sys C₁.sys) :
    prodMapTok (g₀.comp f₀) (g₁.comp f₁) = (prodMapTok g₀ g₁).comp (prodMapTok f₀ f₁) := by
  apply ApproximableMap.ext
  intro W W''
  constructor
  · rintro ⟨X, Y, X'', Y'', ⟨X', hf0, hg0⟩, ⟨Y', hf1, hg1⟩, rfl, rfl⟩
    exact ⟨prodTokNbhd X' Y', ⟨X, Y, X', Y', hf0, hf1, rfl, rfl⟩,
      ⟨X', Y', X'', Y'', hg0, hg1, rfl, rfl⟩⟩
  · rintro ⟨W', ⟨X, Y, X', Y', hf0, hf1, rfl, rfl⟩, ⟨X₂, Y₂, X'', Y'', hg0, hg1, hWeq, rfl⟩⟩
    obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective hWeq
    exact ⟨X, Y, X'', Y'', ⟨X', hf0, hg0⟩, ⟨Y', hf1, hg1⟩, rfl, rfl⟩

end Exercise619
end DomainTheory.Neighborhood
