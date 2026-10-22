/-ai
Scott (1982, §4) forms, for each consistent finite set of tokens, the basic open of those elements of an information system that contain the set. These basic opens are a neighbourhood system on the domain, in the direction converse to the passage from neighbourhood systems to information systems, and the abbreviation infoSys_to_neighborhoodSystem names that system. Its filters recover the original elements.
ai-/
module

public import Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.BridgeTheorems.toNeighborhoodSystem
public import DomainTheory.BridgeTheorems.toFilter
public import DomainTheory.BridgeTheorems.ofFilter
public import DomainTheory.BridgeTheorems.InfoSysToNeighborhood.domainOrderIso
public import DomainTheory.BridgeTheorems.basicOpen_empty
public import DomainTheory.BridgeTheorems.mem_basicOpen_singleton
public import DomainTheory.BridgeTheorems.funion_singleton_eq_insert
public import DomainTheory.BridgeTheorems.basicOpen_singleton_inter
public import DomainTheory.BridgeTheorems.ent_of_basicOpen_subset
public import DomainTheory.BridgeTheorems.con_of_basicOpen_subset
public import DomainTheory.BridgeTheorems.mem_basicOpen_of_singletons
public import DomainTheory.BridgeTheorems.mem_basicOpen_iff
public import DomainTheory.BridgeTheorems.toFilter_ofFilter
public import DomainTheory.BridgeTheorems.ofFilter_toFilter

@[expose] public section

/-!
# Information systems → neighbourhood systems (1982 → 1980)

Scott (1982, §4): for `u ∈ Con`, the basic open
`[u] = { x ∈ |A| | u ⊆ x }` yields a neighbourhood system on the domain `|A|`
whose filters recover the original elements. This is the converse direction to
`NeighborhoodToInfoSys`.
-/

namespace DomainTheory.BridgeTheorems

open DomainTheory.NeighbourhoodSystems
open DomainTheory.InformationSystems
open DomainTheory.InformationSystems.Constructive
open DomainTheory.InformationSystems.InfoSys

namespace InfoSysToNeighborhood

variable {α : Type*} [DecidableEq α] (A : InfoSys α)


end InfoSysToNeighborhood

/-- Blueprint-facing name for the 1982 → 1980 basic-open neighbourhood system. -/
abbrev infoSys_to_neighborhoodSystem {α : Type*} [DecidableEq α] (A : InfoSys α) :
    NeighborhoodSystem A.Element :=
  InfoSysToNeighborhood.toNeighborhoodSystem A

end DomainTheory.BridgeTheorems
