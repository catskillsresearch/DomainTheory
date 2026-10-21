/-ai
The least single-step map from Y to Z relates neighbourhoods Y' and Z' if and only if the single-step output intersection at Y' is contained in Z'.

Unfolding the least step, the relation of the least map is neighbourhood membership of both sets together with that inclusion. Each direction keeps or restores the given membership hypotheses around the inclusion.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise321.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}







/-- `f₀ = leastStep Y Z` relates `Y'` to `Z'` iff (`Y' ⊆ Y` and `Z ⊆ Z'`) or `Z' = Δ₂`. -/
theorem leastStep_rel {Y : Set α} {Z : Set β} (hY : V₀.mem Y) (hZ : V₁.mem Z)
    {Y' : Set α} {Z' : Set β} (hY' : V₀.mem Y') (hZ' : V₁.mem Z') :
    (leastStep Y Z hY hZ).rel Y' Z' ↔ interYs V₁.master [(Y, Z)] Y' ⊆ Z' := by
  rw [leastStep, leastMap_rel]
  exact ⟨fun h => h.2.2, fun h => ⟨hY', hZ', h⟩⟩

end DomainTheory.NeighbourhoodSystems
