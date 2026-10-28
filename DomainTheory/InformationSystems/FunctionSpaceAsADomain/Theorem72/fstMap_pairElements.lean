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

theorem fstMap_pairElements (x : A.Element) (y : B.Element) :
    (fstMap A B).toElement (pairElements A B x y) = x := by
  apply le_antisymm
  · intro a ⟨s, hs, ⟨hCon, _, hEnt⟩⟩
    have hsub : ↑(fstFinset A B s) ⊆ x.carrier := by
      intro b hb
      rcases (mem_fstFinset A B).1 hb with ⟨p, hp, hbot, rfl⟩
      exact (hs (Finset.mem_coe.2 hp)).1 hbot
    exact x.closed _ a hsub (hEnt a (Finset.mem_singleton_self _))
  · intro a ha
    refine ⟨liftLeft A B {a}, ?_, ?_⟩
    · intro p hp
      rcases (mem_liftLeft A B).1 (Finset.mem_coe.1 hp) with ⟨b, hb, rfl⟩
      have : b = a := Finset.mem_singleton.mp hb
      subst this
      exact ⟨fun _ => ha, fun _ => factoid_3_2 B y⟩
    · refine ⟨ProdCon_liftLeft A B (A.con_sing a), A.con_sing a, ?_⟩
      rw [fstFinset_liftLeft]
      exact proposition_2_3_iii A (A.con_sing a)

end InfoSys
end DomainTheory.InformationSystems
