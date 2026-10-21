/-ai
This file gathers and re-exports approximable maps, algebraicity, Scott-continuous maps, basic opens, the passages between approximable maps and Scott-continuous maps, monotonicity, and preservation of directed suprema, as the setting for Scott's Factoid 4.6. The basic opens of finite token sets are the sets of elements containing those tokens, the domain of elements is T₀, an approximable map induces a Scott-continuous function on elements, and a Scott-continuous map arises from the approximable relation that holds when the output finite set is contained in the image of the closure of the input.
ai-/

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
