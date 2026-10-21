/-ai
Every element of a separated sum is the bottom element, the left image of some element of the left system, or the right image of some element of the right system.

Classically, if some left token lies in the element, the left extraction at that token is an element whose left image equals the original element. Otherwise, if some right token lies in the element, the right extraction supplies a right image equal to it. If neither sort of token occurs, the element equals the bottom element.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import Mathlib.Order.Sum.Order
import all Mathlib.Order.Sum.Order
public import Mathlib.Order.WithBot
import all Mathlib.Order.WithBot
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

namespace InfoSysConstructions

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β)

/-- Every sum element is ⊥, a pure left copy, or a pure right copy. Classical. -/
theorem sum_element_trichotomy (z : (sumSystem A B).Element) :
    z = (sumSystem A B).botElement ∨
      (∃ x : A.Element, z = (inlMap A B).toElement x) ∨
        (∃ y : B.Element, z = (inrMap A B).toElement y) := by
  classical
  by_cases hL : ∃ x : α, SumToken.left x ∈ z.carrier
  · obtain ⟨x0, hx0⟩ := hL
    exact Or.inr (Or.inl ⟨sumElementLft A B z x0 hx0, (inlMap_toElement_sumElementLft A B z x0 hx0).symm⟩)
  · by_cases hR : ∃ y : β, SumToken.right y ∈ z.carrier
    · obtain ⟨y0, hy0⟩ := hR
      exact Or.inr (Or.inr ⟨sumElementRht A B z y0 hy0, (inrMap_toElement_sumElementRht A B z y0 hy0).symm⟩)
    · exact Or.inl (eq_botElement_of_no_injections A B z
        (fun x hx => hL ⟨x, hx⟩) (fun y hy => hR ⟨y, hy⟩))

end InfoSysConstructions

end DomainTheory.BridgeTheorems
