/-ai
The finite approximants of an element are the closures of the consistent finite sets of tokens contained in its carrier.
ai-/

module

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid36
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid44

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- Finite approximations of `x`: the set `{ū | u ∈ Con, u ⊆ x}`. -/
def finiteApproximants (x : sys.Element) : Set sys.Element :=
  {y | ∃ (u : Finset α) (hu : u ∈ sys.Con), ↑u ⊆ x.carrier ∧ y = sys.closure u hu}

end InfoSys

end DomainTheory.InformationSystems
