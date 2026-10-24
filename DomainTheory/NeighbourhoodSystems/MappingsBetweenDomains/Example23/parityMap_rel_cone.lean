module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.trueElt
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.falseElt
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.botElt
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.valElt
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.scan
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.parityMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.T
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.botElt_le
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.scan_nil
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.scan_true
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.scan_false
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.scan_append
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.valElt_scan_mono

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example23

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **`parityMap`'s relation on a cone, read off.** `cone σ f Y ↔ Y ∈ valElt(scan σ)` — the
defining existential collapses since a cone has a *unique* generating prefix (`cone_injective`).
(Used throughout Exercise 2.16's uniqueness argument.) -/
theorem parityMap_rel_cone (σ : Str) (Y : Set Example12.Token) :
    parityMap.rel (cone σ) Y ↔ (valElt (scan σ)).mem Y := by
  constructor
  · rintro ⟨ρ, hρ, hval⟩
    rw [cone_injective hρ]
    exact hval
  · intro hval
    exact ⟨σ, rfl, hval⟩

end DomainTheory.NeighbourhoodSystems.Example23
