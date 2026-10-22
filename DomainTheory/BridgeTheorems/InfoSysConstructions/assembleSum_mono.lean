module

public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Sum.Order
public import Mathlib.Order.WithBot
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64
public import DomainTheory.BridgeTheorems.InfoSysConstructions.assembleSum

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

namespace InfoSysConstructions

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β)

theorem assembleSum_mono {w₁ w₂ : WithBot (A.Element ⊕ B.Element)} (h : w₁ ≤ w₂) :
    assembleSum A B w₁ ≤ assembleSum A B w₂ := by
  cases w₁ with
  | bot => exact botElement_le _ _
  | coe s₁ =>
    cases w₂ with
    | bot => exact (WithBot.not_coe_le_bot _ h).elim
    | coe s₂ =>
      have hs : s₁ ≤ s₂ := WithBot.coe_le_coe.1 h
      cases s₁ with
      | inl x =>
        cases s₂ with
        | inl x' => exact (inlMap A B).toElement_mono (Sum.inl_le_inl_iff.1 hs)
        | inr y' => exact (Sum.not_inl_le_inr hs).elim
      | inr y =>
        cases s₂ with
        | inl x' => exact (Sum.not_inr_le_inl hs).elim
        | inr y' => exact (inrMap A B).toElement_mono (Sum.inr_le_inr_iff.1 hs)

end InfoSysConstructions

end DomainTheory.BridgeTheorems
