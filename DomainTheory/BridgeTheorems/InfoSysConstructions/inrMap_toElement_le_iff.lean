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

theorem inrMap_toElement_le_iff {x y : B.Element} :
    (inrMap A B).toElement x ≤ (inrMap A B).toElement y ↔ x ≤ y := by
  constructor
  · intro h b hb
    have : SumToken.right b ∈ ((inrMap A B).toElement x).carrier := by
      have hx := sumElementRht_inrMap_toElement A B x
      have : b ∈ (sumElementRht A B ((inrMap A B).toElement x) B.bot
          (right_bot_mem_inrMap_toElement A B x)).carrier := by
        simpa [hx] using hb
      exact this
    exact (sumElementRht_inrMap_toElement A B y) ▸
      (show b ∈ (sumElementRht A B ((inrMap A B).toElement y) B.bot
          (right_bot_mem_inrMap_toElement A B y)).carrier from h this)
  · exact (inrMap A B).toElement_mono

end InfoSysConstructions

end DomainTheory.BridgeTheorems
