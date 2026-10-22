module

public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Sum.Order
public import Mathlib.Order.WithBot
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64
public import DomainTheory.BridgeTheorems.InfoSysConstructions.right_bot_mem_inrMap_toElement
public import DomainTheory.BridgeTheorems.InfoSysConstructions.sumElementRht_inrMap_toElement

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

namespace InfoSysConstructions

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β)

theorem inrMap_toElement_injective :
    Function.Injective (inrMap A B).toElement := by
  intro x y h
  refine le_antisymm ?_ ?_
  · intro b hb
    have hx := sumElementRht_inrMap_toElement A B x
    have : SumToken.right b ∈ ((inrMap A B).toElement x).carrier := by
      rw [← hx] at hb; exact hb
    rw [h] at this
    have hy := sumElementRht_inrMap_toElement A B y
    have : b ∈ (sumElementRht A B ((inrMap A B).toElement y) B.bot
        (right_bot_mem_inrMap_toElement A B y)).carrier := this
    rwa [hy] at this
  · intro b hb
    have hy := sumElementRht_inrMap_toElement A B y
    have : SumToken.right b ∈ ((inrMap A B).toElement y).carrier := by
      rw [← hy] at hb; exact hb
    rw [← h] at this
    have hx := sumElementRht_inrMap_toElement A B x
    have : b ∈ (sumElementRht A B ((inrMap A B).toElement x) B.bot
        (right_bot_mem_inrMap_toElement A B x)).carrier := this
    rwa [hx] at this

end InfoSysConstructions

end DomainTheory.BridgeTheorems
