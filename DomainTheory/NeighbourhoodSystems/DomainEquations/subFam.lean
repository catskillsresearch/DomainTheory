/-ai
The family of neighbourhood-sets of the subdomains of a neighbourhood system E consists of those collections of sets that are exactly the neighbourhoods of some subsystem of E.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise222

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Proposition611

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set DomainTheory.NeighbourhoodSystems.Exercise222

variable {α : Type*}

/-- The family of **neighbourhood-sets of subdomains of `E`**: a set of subsets of `Δ` lies in
`subFam E` exactly when it is `{X ∣ D.mem X}` for some subsystem `D ◁ E`. This is the concrete
family of sets that, by Exercise 2.22, represents `{D ∣ D ◁ E}` as a domain. -/
def subFam (E : NeighborhoodSystem α) : Set (Set (Set α)) :=
  {𝒮 | ∃ D : NeighborhoodSystem α, D ◁ E ∧ 𝒮 = {X | D.mem X}}

end DomainTheory.NeighbourhoodSystems.Proposition611
