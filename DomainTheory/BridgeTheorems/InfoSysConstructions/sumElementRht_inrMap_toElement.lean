module

public import DomainTheory.BridgeTheorems.InfoSysConstructions.right_bot_mem_inrMap_toElement
public import DomainTheory.BridgeTheorems.InfoSysConstructions.lftFinset_singleton_right
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.sumElementRht
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.rhtFinset
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

theorem sumElementRht_inrMap_toElement (y : B.Element) :
    sumElementRht A B ((inrMap A B).toElement y) B.bot
      (right_bot_mem_inrMap_toElement A B y) = y := by
  apply le_antisymm
  · intro b hb
    obtain ⟨w, hw, ⟨hwCon, hSum, hl, hEnt⟩⟩ := hb
    have hEntB : B.Ent w b := by
      have : rhtFinset ({SumToken.right b} : Finset (SumToken α β)) = {b} :=
        rhtFinset.singleton_right b
      simpa [this] using hEnt b (Finset.mem_singleton_self b)
    exact y.closed w b hw hEntB
  · intro b hb
    change SumToken.right b ∈ ((inrMap A B).toElement y).carrier
    refine ⟨{b}, ?_, ?_⟩
    · intro c hc
      have : c = b := Finset.mem_singleton.mp (Finset.mem_coe.1 hc)
      subst this; exact hb
    · refine ⟨B.con_sing b, Or.inr ⟨lftFinset_singleton_right (α := α) b,
        by rw [rhtFinset.singleton_right]; exact B.con_sing b⟩,
        lftFinset_singleton_right (α := α) b, ?_⟩
      rw [rhtFinset.singleton_right]
      exact proposition_2_3_iii B (B.con_sing b)

end InfoSysConstructions

end DomainTheory.BridgeTheorems
