module

public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41

@[expose] public section

namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- Carrier intersection of a family of elements. -/
def familyInfCarrier (S : Set sys.Element) : Set α :=
  {a | ∀ x ∈ S, a ∈ x.carrier}

end InfoSys

end DomainTheory.InformationSystems
