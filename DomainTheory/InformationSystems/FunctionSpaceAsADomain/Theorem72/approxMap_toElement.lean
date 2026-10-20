module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid32
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.approxMap_toElement_consistent
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.approxMap_toElement_closed

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

/-- **Theorem 7.2.** Approximable map as an element of `|A → B|`. -/
def approxMap_toElement (f : ApproximableMap A B) : (functionSystem A B).Element where
  carrier := {p : FunToken A B | f.rel p.val.1 p.val.2}
  consistent := approxMap_toElement_consistent A B f
  closed := approxMap_toElement_closed A B f

end InfoSys

end DomainTheory.InformationSystems
