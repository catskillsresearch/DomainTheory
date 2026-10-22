/-ai
The map ofFilter sends a filter in the neighbourhood system of an information system to the information-system element whose carrier consists of those tokens whose singleton basic open belongs to the filter. A finite set of such tokens is consistent because the filter meets its basic open, that open contains a basic open of some consistent set, and a basic-open inclusion preserves consistency. If the set entails a further token, its basic open is contained in the singleton basic open of that token, since elements are closed under the entailment, and upward closure puts the token in the carrier.
ai-/
module

public import Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.BridgeTheorems.con_of_basicOpen_subset
public import DomainTheory.BridgeTheorems.toNeighborhoodSystem
public import DomainTheory.BridgeTheorems.mem_basicOpen_of_singletons

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.NeighbourhoodSystems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

namespace InfoSysToNeighborhood

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

def ofFilter (f : (toNeighborhoodSystem A).Element) : A.Element where
  carrier := {a | f.mem (A.basicOpen ({a} : Finset α))}
  consistent := by
    intro Y hY
    have hmem : f.mem (A.basicOpen Y) :=
      mem_basicOpen_of_singletons A f fun a ha => hY (Finset.mem_coe.2 ha)
    obtain ⟨u, hu, heq⟩ := f.sub hmem
    have hsub : A.basicOpen u ⊆ A.basicOpen Y := by
      intro x hx; exact heq ▸ hx
    exact con_of_basicOpen_subset A hu hsub
  closed := by
    intro Y b hY hEnt
    have hmemY : f.mem (A.basicOpen Y) :=
      mem_basicOpen_of_singletons A f fun c hc => hY (Finset.mem_coe.2 hc)
    have hsub : A.basicOpen Y ⊆ A.basicOpen ({b} : Finset α) := by
      intro x hx c hc
      have eqcb : c = b := Finset.mem_singleton.mp (Finset.mem_coe.1 hc)
      rw [eqcb]
      exact x.closed Y b hx hEnt
    exact f.up_mem hmemY ⟨({b} : Finset α), A.con_sing b, rfl⟩ hsub

end InfoSysToNeighborhood

end DomainTheory.BridgeTheorems
