module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import Mathlib.Order.Sum.Order
import all Mathlib.Order.Sum.Order
public import Mathlib.Order.WithBot
import all Mathlib.Order.WithBot
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64
public import DomainTheory.BridgeTheorems.InfoSysConstructions.sum_element_trichotomy
public import DomainTheory.BridgeTheorems.InfoSysConstructions.assembleSum

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

namespace InfoSysConstructions

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β)

/-- Every sum-domain element has a separated-sum code. -/
theorem exists_assembleSum_eq (z : (sumSystem A B).Element) :
    ∃ w : WithBot (A.Element ⊕ B.Element), assembleSum A B w = z := by
  rcases sum_element_trichotomy A B z with hbot | ⟨x, hx⟩ | ⟨y, hy⟩
  · exact ⟨⊥, hbot.symm⟩
  · exact ⟨some (.inl x), hx.symm⟩
  · exact ⟨some (.inr y), hy.symm⟩

end InfoSysConstructions

end DomainTheory.BridgeTheorems
