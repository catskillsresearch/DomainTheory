module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid32
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.mkFunToken_eq

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)


open ApproximableMap


theorem approxMap_toElement_element_toApproxMap (x : (functionSystem A B).Element) :
    approxMap_toElement A B (element_toApproxMap A B x) = x := by
  apply le_antisymm
  · intro p hp
    change (element_toApproxMap A B x).rel p.val.1 p.val.2 at hp
    obtain ⟨_, _, hmem⟩ := hp
    simpa [mkFunToken_eq A B p] using hmem
  · intro p hp
    change (element_toApproxMap A B x).rel p.val.1 p.val.2
    refine ⟨p.property.1, p.property.2, ?_⟩
    simpa [mkFunToken_eq A B p] using hp

end InfoSys
end DomainTheory.InformationSystems
