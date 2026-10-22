module
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.inrMap_toElement_sumElementRht
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.inlMap_toElement_sumElementLft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.eq_botElement_of_no_injections
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.inrMap
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.inlMap
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33.botElement
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable.toElement
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
