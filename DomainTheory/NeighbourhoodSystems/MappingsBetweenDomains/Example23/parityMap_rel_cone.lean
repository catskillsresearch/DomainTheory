/-ai
The parity map relates the cone of a string to a neighbourhood exactly when that neighbourhood belongs to the element selected by scanning the string.

A relation witness is some prefix with the same cone, and cones determine their prefixes, so the witness is the given string. Conversely that string is a witness.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.Basic

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
