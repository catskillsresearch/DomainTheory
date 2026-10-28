module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid32
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.mkFunToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.approxMap_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.element_toApproxMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.applyMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.liftPair
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.curryMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.pairElements
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.uncurryMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.funion_self
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.funion_comm_β
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.rel_input_output_union
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.funCon_of_approxMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.ProdCon_liftPair
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.fstFinset_liftPair
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.sndFinset_liftPair
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.entSet_liftPair
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.rel_of_funTokens
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.funCon_of_curry_pointwise

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
    simpa [mkFunToken.eq A B p] using hmem
  · intro p hp
    change (element_toApproxMap A B x).rel p.val.1 p.val.2
    refine ⟨p.property.1, p.property.2, ?_⟩
    simpa [mkFunToken.eq A B p] using hp

end InfoSys
end DomainTheory.InformationSystems
