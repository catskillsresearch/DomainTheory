/-ai
Recovering an approximable map from the function-space element associated with it returns the original map.

Extensionality of relations is used. A pair related by the recovered map has, as its membership witness, the original relation. A pair related by the original map is consistent on both sides by the domain and codomain laws, and that same relation is the membership witness in the associated element.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid32
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.Basic

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











theorem element_toApproxMap_approxMap_toElement (f : ApproximableMap A B) :
    element_toApproxMap A B (approxMap_toElement A B f) = f := by
  refine ApproximableMap.ext fun u v => ?_
  constructor
  · rintro ⟨hu, hv, hp⟩
    change f.rel u v at hp
    exact hp
  · intro hrel
    exact ⟨f.rel_dom hrel, f.rel_cod hrel, by
      change f.rel u v
      exact hrel⟩

end InfoSys
end DomainTheory.InformationSystems
