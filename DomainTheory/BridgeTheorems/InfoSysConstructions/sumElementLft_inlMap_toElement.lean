module

public import DomainTheory.BridgeTheorems.InfoSysConstructions.left_bot_mem_inlMap_toElement
public import DomainTheory.BridgeTheorems.InfoSysConstructions.rhtFinset_singleton_left
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.sumElementLft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.lftFinset
public import DomainTheory.InformationSystems.InformationSystems.Proposition23.proposition_2_3_iii
public import DomainTheory.InformationSystems.InformationSystems.InfoSys.Basic
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Sum.Order
public import Mathlib.Order.WithBot
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

namespace InfoSysConstructions

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β)

theorem sumElementLft_inlMap_toElement (x : A.Element) :
    sumElementLft A B ((inlMap A B).toElement x) A.bot
      (left_bot_mem_inlMap_toElement A B x) = x := by
  apply le_antisymm
  · intro a ha

    obtain ⟨u, hu, ⟨huCon, hSum, hr, hEnt⟩⟩ := ha
    have hEntA : A.Ent u a := by
      have : lftFinset ({SumToken.left a} : Finset (SumToken α β)) = {a} :=
        lftFinset.singleton_left a
      simpa [this] using hEnt a (Finset.mem_singleton_self a)
    exact x.closed u a hu hEntA
  · intro a ha
    change SumToken.left a ∈ ((inlMap A B).toElement x).carrier
    refine ⟨{a}, ?_, ?_⟩
    · intro b hb
      have : b = a := Finset.mem_singleton.mp (Finset.mem_coe.1 hb)
      subst this; exact ha
    · refine ⟨A.con_sing a, Or.inl ⟨by rw [lftFinset.singleton_left]; exact A.con_sing a,
        rhtFinset_singleton_left (β := β) a⟩, rhtFinset_singleton_left (β := β) a, ?_⟩
      rw [lftFinset.singleton_left]
      exact proposition_2_3_iii A (A.con_sing a)

end InfoSysConstructions

end DomainTheory.BridgeTheorems
