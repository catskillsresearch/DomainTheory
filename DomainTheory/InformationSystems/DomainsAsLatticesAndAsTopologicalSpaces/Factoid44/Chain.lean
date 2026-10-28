module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

class Chain (S : Set sys.Element) : Prop where
  out : ∀ (x y : sys.Element), x ∈ S → y ∈ S → x ≤ y ∨ y ≤ x

end InfoSys

end DomainTheory.InformationSystems
