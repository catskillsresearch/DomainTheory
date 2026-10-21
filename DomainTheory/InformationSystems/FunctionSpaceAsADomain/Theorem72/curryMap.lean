/-ai
Scott's Theorem 7.2 sends an approximable map h from the product of A and B into C to the approximable map from A into the function space B → C that relates a consistent set u to a set of function tokens when h relates the lifted pair of u with the input of each token to the output of that token. Codomain consistency, the empty relation, closure under union, and monotonicity are proved from the pointwise relations by the union and entailment lemmas for lifted pairs.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid32
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.liftPair
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.ProdCon_liftPair
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

/-- **Theorem 7.2.** Approximable `curry h : A → (B → C)`. -/
def curryMap (h : ApproximableMap (productSystem A B) C) :
    ApproximableMap A (functionSystem B C) where
  rel u s :=
    u ∈ A.Con ∧ ∀ p ∈ s, h.rel (liftPair A B u p.val.1) p.val.2
  rel_dom hrel := hrel.1
  rel_cod hrel := funCon_of_curry_pointwise A B C h hrel.1 hrel.2
  empty_rel := ⟨A.con_empty, fun _ hp => False.elim (Finset.notMem_empty _ hp)⟩
  union_right := by
    rintro u s s' ⟨hu, hps⟩ ⟨_, hps'⟩
    refine ⟨hu, ?_⟩
    intro p hp
    rcases mem_funion.mp hp with hp | hp
    · exact hps p hp
    · exact hps' p hp
  mono := by
    rintro u u' s s' ⟨hu, hps⟩ hEntu hEnts hu' hs'
    refine ⟨hu', ?_⟩
    intro p hp
    -- FunEnt s p from EntSet
    have hEntp : FunEnt B C s p := hEnts p hp
    obtain ⟨_, t, ht, hIn, hOut⟩ := hEntp
    have hps_t : ∀ q ∈ t, h.rel (liftPair A B u q.val.1) q.val.2 :=
      fun q hq => hps q (ht hq)
    have hin : funInputUnion B C t ∈ B.Con :=
      B.con_subset
        (proposition_2_3_ii B p.property.1 (entSet_inputUnion_of_ent B C hIn))
        (subset_funion_right _ _)
    have hmid : h.rel (liftPair A B u (funInputUnion B C t)) (funOutputUnion B C t) :=
      rel_of_funTokens A B C h u hu t hps_t hin
    have hmid' : h.rel (liftPair A B u' p.val.1) (funOutputUnion B C t) :=
      h.mono hmid
        (entSet_liftPair A B hu' p.property.1 hEntu
          (entSet_inputUnion_of_ent B C hIn))
        (proposition_2_3_iii C (h.rel_cod hmid))
        (ProdCon_liftPair A B hu' p.property.1) (h.rel_cod hmid)
    exact h.mono hmid'
      (proposition_2_3_iii (productSystem A B) (ProdCon_liftPair A B hu' p.property.1))
      hOut (ProdCon_liftPair A B hu' p.property.1) p.property.2

end InfoSys

end DomainTheory.InformationSystems
