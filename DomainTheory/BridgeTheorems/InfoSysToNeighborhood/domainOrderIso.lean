module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.BridgeTheorems.mem_basicOpen_singleton
public import DomainTheory.BridgeTheorems.toNeighborhoodSystem
public import DomainTheory.BridgeTheorems.toFilter
public import DomainTheory.BridgeTheorems.ofFilter
public import DomainTheory.BridgeTheorems.toFilter_ofFilter
public import DomainTheory.BridgeTheorems.ofFilter_toFilter

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.NeighbourhoodSystems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

namespace InfoSysToNeighborhood

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

def domainOrderIso : A.Element ≃o (toNeighborhoodSystem A).Element where
  toFun := toFilter A
  invFun := ofFilter A
  left_inv := ofFilter_toFilter A
  right_inv := toFilter_ofFilter A
  map_rel_iff' := by
    intro x y
    constructor
    · intro h a ha
      have hx : (toFilter A x).mem (A.basicOpen ({a} : Finset α)) :=
        ⟨({a} : Finset α), A.con_sing a, rfl, by
          intro c hc
          have hc' : c = a := Finset.mem_singleton.mp (Finset.mem_coe.1 hc)
          exact hc' ▸ ha⟩
      have hy : (toFilter A y).mem (A.basicOpen ({a} : Finset α)) := h _ hx
      obtain ⟨u, hu, heq, hsub⟩ := hy
      have huA : A.closure u hu ∈ A.basicOpen u := subset_closure A hu
      have hsing : A.closure u hu ∈ A.basicOpen ({a} : Finset α) := by
        rw [heq]; exact huA
      have ha' : a ∈ (A.closure u hu).carrier := (mem_basicOpen_singleton A).1 hsing
      exact y.closed u a hsub ha'
    · intro h U hU
      obtain ⟨u, hu, hUeq, huX⟩ := hU
      subst hUeq
      exact ⟨u, hu, rfl, fun a ha => h (huX ha)⟩

end InfoSysToNeighborhood

end DomainTheory.BridgeTheorems
