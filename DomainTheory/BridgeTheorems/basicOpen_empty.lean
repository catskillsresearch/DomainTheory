/-ai
The basic open of the empty set of tokens is the set of all elements of the information system.

Every element of that basic open is an element. Conversely, the empty set is contained in every element, because no token belongs to the empty set.
ai-/
module

public import Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46
public import DomainTheory.InformationSystems.InformationSystems.Proposition23

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.NeighbourhoodSystems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

namespace InfoSysToNeighborhood

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem basicOpen_empty : A.basicOpen (∅ : Finset α) = (Set.univ : Set A.Element) := by
  ext x
  constructor
  · intro; trivial
  · intro _ a ha
    exact False.elim (Finset.notMem_empty a (Finset.mem_coe.1 ha))

end InfoSysToNeighborhood

end DomainTheory.BridgeTheorems
