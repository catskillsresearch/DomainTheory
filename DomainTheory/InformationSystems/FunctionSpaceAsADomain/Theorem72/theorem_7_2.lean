/-ai
The first sentence of Scott's Theorem 7.2: the approximable maps from an information system A to an information system B are exactly the elements of the function-space system of Definition 7.1. The application and currying clauses of the same numbered theorem are not this statement.

The two conversions, from an approximable map to a function-space element and back, are mutually inverse by the two inverse lemmas.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid32
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.element_toApproxMap_approxMap_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.approxMap_toElement_element_toApproxMap

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)






open ApproximableMap























/-- **Theorem 7.2, first sentence (Scott 1982).** Approximable maps `A → B` are
exactly the elements of the Definition 7.1 function-space system `|A → B|`.
The `apply` / `curry` clauses of the same numbered theorem are proved above
and are not this compared declaration. -/
theorem theorem_7_2 {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]
    (A : InfoSys α) (B : InfoSys β) :
    (∀ f : ApproximableMap A B,
      element_toApproxMap A B (approxMap_toElement A B f) = f) ∧
    (∀ x : (functionSystem A B).Element,
      approxMap_toElement A B (element_toApproxMap A B x) = x) :=
  ⟨element_toApproxMap_approxMap_toElement A B,
    approxMap_toElement_element_toApproxMap A B⟩

end InfoSys
end DomainTheory.InformationSystems
