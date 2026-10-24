module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.SatisfiesRunEquations
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.del
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.out
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.runMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.del_nil
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.del_true
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.del_false
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.out_nil
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.out_false
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.out_true
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.del_append
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.out_append
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.out_mono

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **`runMap`'s relation on a cone, read off.** `σΣ* g Y ↔ Y ∈ B ∧ (out σ)Σ* ⊆ Y` — the defining
existential collapses since a cone has a *unique* generating prefix (`cone_injective`). -/
theorem runMap_rel_cone (σ : Str) (Y : Set Str) :
    runMap.rel (cone σ) Y ↔ B.mem Y ∧ cone (out σ) ⊆ Y := by
  constructor
  · rintro ⟨ρ, hρ, hYmem, hsub⟩
    obtain rfl : ρ = σ := (cone_injective hρ).symm
    exact ⟨hYmem, hsub⟩
  · rintro ⟨hYmem, hsub⟩
    exact ⟨σ, rfl, hYmem, hsub⟩

end DomainTheory.NeighbourhoodSystems.Example24
