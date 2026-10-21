/-ai
The carrier union of a family of elements is the set of tokens that belong to the carrier of some element of the family.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid42

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- Carrier union of a family of elements. -/
def familyUnionCarrier (S : Set sys.Element) : Set α :=
  {a | ∃ x ∈ S, a ∈ x.carrier}

end InfoSys

end DomainTheory.InformationSystems
