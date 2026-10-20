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







/-- **`(I_{𝒟₀} × I_{𝒟₁}) = I_{𝒟₀×𝒟₁}`.** -/
theorem prodMapTok_id :
    prodMapTok (idMap A₀.sys) (idMap A₁.sys) = idMap (A₀.prod A₁).sys := by
  apply ApproximableMap.ext
  intro W W'
  constructor
  · rintro ⟨X, Y, X', Y', ⟨hX, hX', hsX⟩, ⟨hY, hY', hsY⟩, rfl, rfl⟩
    exact ⟨prodTok_mem_prodTokNbhd hX hY, prodTok_mem_prodTokNbhd hX' hY',
      prodTokNbhd_subset_iff.mpr ⟨hsX, hsY⟩⟩
  · rintro ⟨⟨X, Y, hX, hY, rfl⟩, ⟨X', Y', hX', hY', rfl⟩, hsub⟩
    obtain ⟨hsX, hsY⟩ := prodTokNbhd_subset_iff.mp hsub
    exact ⟨X, Y, X', Y', ⟨hX, hX', hsX⟩, ⟨hY, hY', hsY⟩, rfl, rfl⟩

end Exercise619
end DomainTheory.Neighborhood
