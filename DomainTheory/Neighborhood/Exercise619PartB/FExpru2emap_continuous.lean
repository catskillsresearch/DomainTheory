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
import DomainTheory.Neighborhood.Exercise619PartB.FExpru2emap_mono
import DomainTheory.Neighborhood.Exercise619PartB.FExpru2emap_continuous_mp


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise619
open DomainTheory.Neighborhood.Example62 DomainTheory.Neighborhood.ExampleB
open DomainTheory.Neighborhood.Exercise510

namespace Exercise619





variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}















/-- **`λf. T(f)` is continuous on maps.** For a non-empty directed family `gᵢ` with pointwise union
`f`, the relation of `T(f)` is the union of those of the `T(gᵢ)` — `T(f)` is approximable. -/
theorem FExpr.map_continuous (T : FExpr) {I : Type} [Nonempty I] {X Y : ScottSys}
    (g : I → ApproximableMap X.sys Y.sys) (f : ApproximableMap X.sys Y.sys)
    (hdir : ∀ i j, ∃ k, g i ≤ g k ∧ g j ≤ g k)
    (hf : ∀ A B, f.rel A B ↔ ∃ i, (g i).rel A B) (A B : Set Str) :
    (T.map f).rel A B ↔ ∃ i, (T.map (g i)).rel A B := by
  refine ⟨T.map_continuous_mp hdir hf, ?_⟩
  rintro ⟨i, hi⟩
  have hgif : g i ≤ f := by
    rw [ApproximableMap.le_iff]; intro A' B' h; exact (hf A' B').mpr ⟨i, h⟩
  exact (T.map_mono hgif) A B hi

end Exercise619
end DomainTheory.Neighborhood
