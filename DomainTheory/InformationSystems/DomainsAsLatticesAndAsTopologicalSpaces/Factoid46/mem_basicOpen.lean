module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]


theorem mem_basicOpen {A : InfoSys α} {u : Finset α} {x : A.Element} :
    x ∈ A.basicOpen u ↔ ↑u ⊆ x.carrier := Iff.rfl

end InfoSys
end DomainTheory.InformationSystems
