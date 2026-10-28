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

theorem sndMap_pairElements (x : A.Element) (y : B.Element) :
    (sndMap A B).toElement (pairElements A B x y) = y := by
  apply le_antisymm
  · intro b ⟨s, hs, ⟨hCon, _, hEnt⟩⟩
    have hsub : ↑(sndFinset A B s) ⊆ y.carrier := by
      intro c hc
      rcases (mem_sndFinset A B).1 hc with ⟨p, hp, hbot, rfl⟩
      exact (hs (Finset.mem_coe.2 hp)).2 hbot
    exact y.closed _ b hsub (hEnt b (Finset.mem_singleton_self _))
  · intro b hb
    refine ⟨liftRight A B {b}, ?_, ?_⟩
    · intro p hp
      rcases (mem_liftRight A B).1 (Finset.mem_coe.1 hp) with ⟨c, hc, rfl⟩
      have : c = b := Finset.mem_singleton.mp hc
      subst this
      exact ⟨fun _ => factoid_3_2 A x, fun _ => hb⟩
    · refine ⟨ProdCon_liftRight A B (B.con_sing b), B.con_sing b, ?_⟩
      rw [sndFinset_liftRight]
      exact proposition_2_3_iii B (B.con_sing b)

end InfoSys
end DomainTheory.InformationSystems
