/-ai
A filter in the neighbourhood system of an information system meets the basic open of a consistent finite set if and only if that set is contained in the carrier of the information-system element recovered from the filter.

If the filter meets the basic open, then for each token of the set the basic open is contained in the basic open of the corresponding singleton, so upward closure puts the token in the recovered carrier. Conversely, containment in the recovered carrier means the filter meets each singleton basic open, and the lemma on singletons yields membership in the basic open of the whole set.
ai-/
module

public import Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.BridgeTheorems.toNeighborhoodSystem
public import DomainTheory.BridgeTheorems.mem_basicOpen_of_singletons
public import DomainTheory.BridgeTheorems.ofFilter

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.NeighbourhoodSystems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

namespace InfoSysToNeighborhood

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem mem_basicOpen_iff (f : (toNeighborhoodSystem A).Element) {u : Finset α}
    (_hu : u ∈ A.Con) :
    f.mem (A.basicOpen u) ↔ ↑u ⊆ (ofFilter A f).carrier := by
  constructor
  · intro h a ha
    have hsub : A.basicOpen u ⊆ A.basicOpen ({a} : Finset α) := by
      intro x hx c hc
      have hc' : c = a := Finset.mem_singleton.mp (Finset.mem_coe.1 hc)
      subst hc'
      exact hx (Finset.mem_coe.2 ha)
    exact f.up_mem h ⟨({a} : Finset α), A.con_sing a, rfl⟩ hsub
  · intro hsub
    exact mem_basicOpen_of_singletons A f fun a ha => hsub (Finset.mem_coe.2 ha)

end InfoSysToNeighborhood

end DomainTheory.BridgeTheorems
