/-ai
The formal union of a singleton token a with a finite set s is the insertion of a into s.

A token of the formal union lies in the singleton, hence is a, or already lies in s. A token of the insertion is a, hence lies in the singleton side, or lies in s, hence lies in the other side.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
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

theorem funion_singleton_eq_insert (a : α) (s : Finset α) :
    ({a} : Finset α) ∪' s = insert a s := by
  ext x
  constructor
  · intro hx
    rcases mem_funion.mp hx with h | h
    · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp h))
    · exact Finset.mem_insert_of_mem h
  · intro hx
    rcases Finset.mem_insert.mp hx with h | h
    · exact mem_funion.mpr (Or.inl (h ▸ Finset.mem_singleton_self a))
    · exact mem_funion.mpr (Or.inr h)

end InfoSysToNeighborhood

end DomainTheory.BridgeTheorems
