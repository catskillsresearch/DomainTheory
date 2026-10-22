module

public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Sum.Order
public import Mathlib.Order.WithBot
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64
public import DomainTheory.BridgeTheorems.InfoSysConstructions.left_bot_mem_inlMap_toElement
public import DomainTheory.BridgeTheorems.InfoSysConstructions.right_bot_mem_inrMap_toElement
public import DomainTheory.BridgeTheorems.InfoSysConstructions.assembleSum
public import DomainTheory.BridgeTheorems.InfoSysConstructions.classifySum
public import DomainTheory.BridgeTheorems.InfoSysConstructions.assembleSum_classifySum
public import DomainTheory.BridgeTheorems.InfoSysConstructions.not_left_mem_sum_botElement
public import DomainTheory.BridgeTheorems.InfoSysConstructions.not_right_mem_sum_botElement
public import DomainTheory.BridgeTheorems.InfoSysConstructions.classifySum_assembleSum
public import DomainTheory.BridgeTheorems.InfoSysConstructions.inlMap_toElement_le_iff
public import DomainTheory.BridgeTheorems.InfoSysConstructions.inrMap_toElement_le_iff
public import DomainTheory.BridgeTheorems.InfoSysConstructions.assembleSum_mono

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

namespace InfoSysConstructions

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β)

/-- **Separated-sum domain iso (1982).** `|A + B| ≃o WithBot (|A| ⊕ |B|)`. Classical. -/
noncomputable def sumDomainIso :
    WithBot (A.Element ⊕ B.Element) ≃o (sumSystem A B).Element where
  toFun := assembleSum A B
  invFun := classifySum A B
  left_inv := classifySum_assembleSum A B
  right_inv := assembleSum_classifySum A B
  map_rel_iff' := by
    intro w₁ w₂
    constructor
    · intro h
      cases w₁ with
      | bot => exact bot_le
      | coe s₁ =>
        cases w₂ with
        | bot =>
          cases s₁ with
          | inl x =>
            exact False.elim (not_left_mem_sum_botElement A B
              (h (left_bot_mem_inlMap_toElement A B x)))
          | inr y =>
            exact False.elim (not_right_mem_sum_botElement A B
              (h (right_bot_mem_inrMap_toElement A B y)))
        | coe s₂ =>
          refine WithBot.coe_le_coe.2 ?_
          cases s₁ with
          | inl x =>
            cases s₂ with
            | inl x' => exact Sum.inl_le_inl_iff.2 ((inlMap_toElement_le_iff A B).1 h)
            | inr y' =>
              exact False.elim <|
                not_mem_right_of_mem_left A B ((inrMap A B).toElement y')
                  (h (left_bot_mem_inlMap_toElement A B x))
                  (right_bot_mem_inrMap_toElement A B y')
          | inr y =>
            cases s₂ with
            | inl x' =>
              exact False.elim <|
                not_mem_right_of_mem_left A B ((inlMap A B).toElement x')
                  (left_bot_mem_inlMap_toElement A B x')
                  (h (right_bot_mem_inrMap_toElement A B y))
            | inr y' => exact Sum.inr_le_inr_iff.2 ((inrMap_toElement_le_iff A B).1 h)
    · exact assembleSum_mono A B

end InfoSysConstructions

end DomainTheory.BridgeTheorems
