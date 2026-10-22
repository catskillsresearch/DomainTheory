/-ai
An information-system element lies in the basic open of a singleton if and only if the token of that singleton belongs to its carrier.

Membership in the basic open means that every token of the singleton, hence its unique token, lies in the carrier. Conversely, if that token lies in the carrier, it is the only token of the singleton, so the element lies in the basic open.
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

theorem mem_basicOpen_singleton {a : α} {x : A.Element} :
    x ∈ A.basicOpen ({a} : Finset α) ↔ a ∈ x.carrier := by
  constructor
  · intro h
    exact h (Finset.mem_coe.2 (Finset.mem_singleton_self a))
  · intro ha b hb
    have hb' : b = a := Finset.mem_singleton.mp (Finset.mem_coe.1 hb)
    exact hb' ▸ ha

end InfoSysToNeighborhood

end DomainTheory.BridgeTheorems
