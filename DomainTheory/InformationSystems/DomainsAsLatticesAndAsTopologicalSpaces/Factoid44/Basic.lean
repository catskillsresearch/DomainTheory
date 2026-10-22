/-ai
This module gathers and re-exports directed families, chains, directed suprema, chain suprema, the passage from a chain to a directed family, and the lemmas on finite subsets and finite consistency of a directed union, as the setting for Factoid 4.4. The union of a nonempty directed family of elements is again an element and a least upper bound, and unions of increasing chains are elements, so the set of elements is a cpo under inclusion.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid44.IsDirected
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid44.Chain
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid44.directedSup
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid44.chainSup
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid44.IsDirected_of_IsChain
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid44.exists_mem_of_subset_directedUnion
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid44.finitelyConsistent_of_directed

@[expose] public section

/-!
# Factoid 4.4 — directed (and chain) unions are elements

**Factoid 4.4 (Scott §4).** The union of a nonempty directed family of elements is again
an element (hence a lub). In particular, unions of increasing chains are elements, so
`|A|` is a cpo under inclusion.
-/

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)


end InfoSys
end DomainTheory.InformationSystems
