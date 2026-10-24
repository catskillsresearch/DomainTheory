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
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.parityMap_rel_cone

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example23

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **`parityMap`'s elementwise value, read off cone-by-cone.** `f(x).mem Y` iff *some* cone
`σΣ* ∈ x` already witnesses `Y ∈ valElt(scan σ)` — every neighbourhood of `x` is a cone
(`Element.sub`), and `parityMap`'s relation is exactly `parityMap_rel_cone`. -/
theorem parityMap_toElementMap_mem (x : B.Element) (Y : Set Example12.Token) :
    (parityMap.toElementMap x).mem Y ↔ ∃ τ, x.mem (cone τ) ∧ (valElt (scan τ)).mem Y := by
  constructor
  · rintro ⟨X, hX, hrel⟩
    obtain ⟨τ, rfl⟩ := x.sub hX
    exact ⟨τ, hX, (parityMap_rel_cone τ Y).mp hrel⟩
  · rintro ⟨τ, hτ, hval⟩
    exact ⟨cone τ, hτ, (parityMap_rel_cone τ Y).mpr hval⟩

end DomainTheory.NeighbourhoodSystems.Example23
