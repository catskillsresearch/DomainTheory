module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46.ScottContinuous
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46.basicOpen
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46.toScottContinuous
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46.ofScottContinuous
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46.mono
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46.toElement_directedSup

@[expose] public section

/-!
# Factoid 4.6 — Scott topology and continuous maps

**Factoid 4.6 (Scott §4).** Basic opens `[u] = {x | u ⊆ x}` form a neighborhood basis;
`|A|` is `T₀`. Approximable maps induce Scott-continuous functions on elements, and
conversely every Scott-continuous map arises from an approximable relation
(`u f v ↔ ↑v ⊆ f(ū)`).
-/

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]



namespace ScottContinuous

variable {A : InfoSys α} {B : InfoSys β}


end ScottContinuous

namespace ApproximableMap

variable {A : InfoSys α} {B : InfoSys β}



end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
