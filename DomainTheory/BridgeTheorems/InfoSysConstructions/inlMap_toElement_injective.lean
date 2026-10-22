module
public import DomainTheory.BridgeTheorems.InfoSysConstructions.sumElementLft_inlMap_toElement
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.inlMap
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable.toElement
public import DomainTheory.InformationSystems.InformationSystems.InfoSys.Basic
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Sum.Order
public import Mathlib.Order.WithBot
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64
public import DomainTheory.BridgeTheorems.InfoSysConstructions.left_bot_mem_inlMap_toElement


@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

namespace InfoSysConstructions

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β)

theorem inlMap_toElement_injective :
    Function.Injective (inlMap A B).toElement := by
  intro x y h
  refine le_antisymm ?_ ?_
  · intro a ha
    have hx := sumElementLft_inlMap_toElement A B x
    have : SumToken.left a ∈ ((inlMap A B).toElement x).carrier := by
      rw [← hx] at ha; exact ha
    rw [h] at this
    have hy := sumElementLft_inlMap_toElement A B y
    have : a ∈ (sumElementLft A B ((inlMap A B).toElement y) A.bot
        (left_bot_mem_inlMap_toElement A B y)).carrier := this
    rwa [hy] at this
  · intro a ha
    have hy := sumElementLft_inlMap_toElement A B y
    have : SumToken.left a ∈ ((inlMap A B).toElement y).carrier := by
      rw [← hy] at ha; exact ha
    rw [← h] at this
    have hx := sumElementLft_inlMap_toElement A B x
    have : a ∈ (sumElementLft A B ((inlMap A B).toElement x) A.bot
        (left_bot_mem_inlMap_toElement A B x)).carrier := this
    rwa [hx] at this

end InfoSysConstructions

end DomainTheory.BridgeTheorems
