/-ai
If a filter in the neighbourhood system of an information system meets the basic open of every singleton from a finite set, then it meets the basic open of that set.

The proof is by induction on the finite set. The empty basic open is the master set, which every filter meets. When a token is inserted, the filter meets the basic open of that singleton and, by the inductive hypothesis, the basic open of the remainder; their intersection is the basic open of the enlarged set.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.BridgeTheorems.basicOpen_empty
public import DomainTheory.BridgeTheorems.basicOpen_singleton_inter
public import DomainTheory.BridgeTheorems.toNeighborhoodSystem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.NeighbourhoodSystems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

namespace InfoSysToNeighborhood

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem mem_basicOpen_of_singletons (f : (toNeighborhoodSystem A).Element) {Y : Finset α}
    (hY : ∀ a ∈ Y, f.mem (A.basicOpen ({a} : Finset α))) :
    f.mem (A.basicOpen Y) := by
  induction Y using Finset.induction with
  | empty =>
    rw [basicOpen_empty]
    have hmaster : (toNeighborhoodSystem A).master = (Set.univ : Set A.Element) := rfl
    rw [← hmaster]
    exact f.master_mem
  | insert a s _ha ih =>
    have hA := hY a (Finset.mem_insert_self a s)
    have hSm := ih fun i hi => hY i (Finset.mem_insert_of_mem hi)
    simpa [basicOpen_singleton_inter A a s] using f.inter_mem hA hSm

end InfoSysToNeighborhood

end DomainTheory.BridgeTheorems
