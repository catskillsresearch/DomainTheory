/-ai
The run map relates the cone of a string to a set exactly when that set is a neighbourhood and contains the cone of the output of the string.

A relation witness is some prefix with the same cone, and cones determine their prefixes. Conversely the given string is a witness.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.Basic

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
