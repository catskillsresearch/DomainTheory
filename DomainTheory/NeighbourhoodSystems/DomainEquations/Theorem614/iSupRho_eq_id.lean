/-ai
The union of the projections equals the identity map on the colimit.

Relational extensionality applies. A witness at some level gives two neighbourhoods with an intermediate set between them, so the first is contained in the second. If the first neighbourhood is contained in the second and belongs to some level, that same set is the intermediate neighbourhood at that level.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Theorem614


variable {α : Type w}


/-- **`⋃ₙ ρₙ = I_𝒟`** (Scott's key identity for uniqueness). The forward inclusion uses
`X ⊆ z ⊆ Y ⟹ X ⊆ Y`; the reverse factors the identity step `X ⊆ X ⊆ Y` through the level
witnessing `X ∈ 𝒟`. -/
theorem iSupRho_eq_id (s : Setup.{w}) : iSupRho s = idMap (colim s) := by
  apply ApproximableMap.ext
  intro X Y
  rw [idMap_rel]
  constructor
  · rintro ⟨n, hr⟩
    rw [rho_rel] at hr
    obtain ⟨hcX, hcY, z, _, hXz, hzY⟩ := hr
    exact ⟨hcX, hcY, hXz.trans hzY⟩
  · rintro ⟨hcX, hcY, hXY⟩
    obtain ⟨n, hX⟩ := hcX
    exact ⟨n, (rho_rel s n).mpr ⟨⟨n, hX⟩, hcY, X, hX, subset_rfl, hXY⟩⟩

end Theorem614
end DomainTheory.NeighbourhoodSystems
