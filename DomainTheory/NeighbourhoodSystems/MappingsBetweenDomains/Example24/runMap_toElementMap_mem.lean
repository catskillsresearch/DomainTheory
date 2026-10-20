module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.runMap_rel_cone

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB










/-- **`runMap`'s elementwise value, read off cone-by-cone.** `g(x).mem Y` iff *some* cone
`σΣ* ∈ x` already witnesses `Y ∈ B` and `(out σ)Σ* ⊆ Y`. -/
theorem runMap_toElementMap_mem (x : B.Element) (Y : Set Str) :
    (runMap.toElementMap x).mem Y ↔ ∃ τ, x.mem (cone τ) ∧ B.mem Y ∧ cone (out τ) ⊆ Y := by
  constructor
  · rintro ⟨X, hX, hrel⟩
    obtain ⟨τ, rfl⟩ := x.sub hX
    exact ⟨τ, hX, (runMap_rel_cone τ Y).mp hrel⟩
  · rintro ⟨τ, hτ, hYmem, hsub⟩
    exact ⟨cone τ, hτ, (runMap_rel_cone τ Y).mpr ⟨hYmem, hsub⟩⟩

end DomainTheory.NeighbourhoodSystems.Example24
