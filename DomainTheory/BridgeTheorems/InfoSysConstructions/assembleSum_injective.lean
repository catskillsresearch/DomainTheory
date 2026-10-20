/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import Mathlib.Order.Sum.Order
import all Mathlib.Order.Sum.Order
public import Mathlib.Order.WithBot
import all Mathlib.Order.WithBot
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64
public import DomainTheory.BridgeTheorems.InfoSysConstructions.left_bot_mem_inlMap_toElement
public import DomainTheory.BridgeTheorems.InfoSysConstructions.right_bot_mem_inrMap_toElement
public import DomainTheory.BridgeTheorems.InfoSysConstructions.inlMap_toElement_injective
public import DomainTheory.BridgeTheorems.InfoSysConstructions.inrMap_toElement_injective
public import DomainTheory.BridgeTheorems.InfoSysConstructions.assembleSum
public import DomainTheory.BridgeTheorems.InfoSysConstructions.not_left_mem_sum_botElement
public import DomainTheory.BridgeTheorems.InfoSysConstructions.not_right_mem_sum_botElement

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

namespace InfoSysConstructions

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β)

theorem assembleSum_injective :
    Function.Injective (assembleSum A B) := by
  intro w₁ w₂ h
  cases w₁ with
  | bot =>
    cases w₂ with
    | bot => rfl
    | coe s₂ =>
      cases s₂ with
      | inl x =>
        change (sumSystem A B).botElement = (inlMap A B).toElement x at h
        have hx := left_bot_mem_inlMap_toElement A B x
        rw [← h] at hx
        exact False.elim (not_left_mem_sum_botElement A B hx)
      | inr y =>
        change (sumSystem A B).botElement = (inrMap A B).toElement y at h
        have hy := right_bot_mem_inrMap_toElement A B y
        rw [← h] at hy
        exact False.elim (not_right_mem_sum_botElement A B hy)
  | coe s₁ =>
    cases w₂ with
    | bot =>
      cases s₁ with
      | inl x =>
        change (inlMap A B).toElement x = (sumSystem A B).botElement at h
        have hx := left_bot_mem_inlMap_toElement A B x
        rw [h] at hx
        exact False.elim (not_left_mem_sum_botElement A B hx)
      | inr y =>
        change (inrMap A B).toElement y = (sumSystem A B).botElement at h
        have hy := right_bot_mem_inrMap_toElement A B y
        rw [h] at hy
        exact False.elim (not_right_mem_sum_botElement A B hy)
    | coe s₂ =>
      cases s₁ with
      | inl x =>
        cases s₂ with
        | inl x' => exact congrArg (fun t => some (Sum.inl t)) (inlMap_toElement_injective A B h)
        | inr y' =>
          change (inlMap A B).toElement x = (inrMap A B).toElement y' at h
          have hx := left_bot_mem_inlMap_toElement A B x
          rw [h] at hx
          exact False.elim <| not_mem_right_of_mem_left A B ((inrMap A B).toElement y')
            hx
            (right_bot_mem_inrMap_toElement A B y')
      | inr y =>
        cases s₂ with
        | inl x' =>
          change (inrMap A B).toElement y = (inlMap A B).toElement x' at h
          have hy := right_bot_mem_inrMap_toElement A B y
          rw [h] at hy
          exact False.elim <| not_mem_right_of_mem_left A B ((inlMap A B).toElement x')
            (left_bot_mem_inlMap_toElement A B x')
            hy
        | inr y' => exact congrArg (fun t => some (Sum.inr t)) (inrMap_toElement_injective A B h)

end InfoSysConstructions

end DomainTheory.BridgeTheorems
