module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ α' β' : Type*}

/-- The product representation is determined by its two components (the `↔` form of
`prodNbhd_injective`). -/
theorem prodNbhd_eq_iff {X X' : Set α} {Y Y' : Set β} :
    prodNbhd X Y = prodNbhd X' Y' ↔ X = X' ∧ Y = Y' :=
  ⟨prodNbhd_injective, by rintro ⟨rfl, rfl⟩; rfl⟩

end DomainTheory.NeighbourhoodSystems
