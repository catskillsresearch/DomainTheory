module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid32
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.mkFunToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.element_toApproxMap_rel_dom
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.element_toApproxMap_rel_cod
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.element_toApproxMap_empty_rel
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.element_toApproxMap_union_right
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.element_toApproxMap_mono

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

/-- **Theorem 7.2.** Element of `|A → B|` as an approximable map. -/
def element_toApproxMap (x : (functionSystem A B).Element) : ApproximableMap A B where
  rel u v := ∃ (hu : u ∈ A.Con) (hv : v ∈ B.Con), mkFunToken A B u v hu hv ∈ x.carrier
  rel_dom := element_toApproxMap_rel_dom A B x
  rel_cod := element_toApproxMap_rel_cod A B x
  empty_rel := element_toApproxMap_empty_rel A B x
  union_right := element_toApproxMap_union_right A B x
  mono := element_toApproxMap_mono A B x

end InfoSys

end DomainTheory.InformationSystems
