/-ai
The order isomorphism between the elements of an information system and the filters of its basic-open neighbourhood system sends an element to the filter of basic opens contained in it and sends a filter back to the element it determines. The two composites are the identity. If the filter of x is contained in the filter of y and a token a belongs to x, the basic open of the singleton of a belongs to the filter of x, since that singleton is consistent and contained in x, and hence belongs to the filter of y. It is then the basic open of some consistent finite set u contained in y. The closure of u lies in the basic open of u and therefore in the basic open of the singleton, so a belongs to the closure, and closure of y under entailment puts a in y. Conversely, if x lies under y and the basic open of a consistent finite set u belongs to the filter of x, then u is contained in x and hence in y, so the same basic open belongs to the filter of y.
ai-/
module

public import Mathlib.Order.Hom.Basic
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
