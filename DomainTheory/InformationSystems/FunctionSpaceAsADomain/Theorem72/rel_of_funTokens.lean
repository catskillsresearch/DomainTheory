module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid32
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.liftPair
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.ProdCon_liftPair
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.entSet_liftPair

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

/-- Combine pointwise `h`-relations along a finite set of function tokens. -/
theorem rel_of_funTokens (h : ApproximableMap (productSystem A B) C)
    (u : Finset α) (hu : u ∈ A.Con) (t : Finset (FunToken B C))
    (hps : ∀ p ∈ t, h.rel (liftPair A B u p.val.1) p.val.2)
    (hin : funInputUnion B C t ∈ B.Con) :
    h.rel (liftPair A B u (funInputUnion B C t)) (funOutputUnion B C t) := by
  induction t using Finset.induction_on with
  | empty =>
    rw [funInputUnion_empty, funOutputUnion_empty]
    have hdom : liftPair A B u ∅ ∈ (productSystem A B).Con :=
      ProdCon_liftPair A B hu B.con_empty
    exact h.mono h.empty_rel
      ((productSystem A B).entSet_empty _)
      (C.entSet_empty ∅) hdom C.con_empty
  | insert p t' hpnot ih =>
    have hps' : ∀ q ∈ t', h.rel (liftPair A B u q.val.1) q.val.2 :=
      fun q hq => hps q (Finset.mem_insert_of_mem hq)
    have hin' : funInputUnion B C t' ∈ B.Con :=
      B.con_subset hin (by
        rw [funInputUnion_insert]
        exact subset_funion_right _ _)
    have ih' := ih hps' hin'
    have hp : h.rel (liftPair A B u p.val.1) p.val.2 :=
      hps p (Finset.mem_insert_self p t')
    have hinU : p.val.1 ∪' funInputUnion B C t' ∈ B.Con := by
      rwa [funInputUnion_insert] at hin
    have hEnt_p : B.EntSet (p.val.1 ∪' funInputUnion B C t') p.val.1 :=
      fun y hy => B.ent_refl hinU (subset_funion_left _ _ hy)
    have hEnt_t : B.EntSet (p.val.1 ∪' funInputUnion B C t') (funInputUnion B C t') :=
      fun y hy => B.ent_refl hinU (subset_funion_right _ _ hy)
    have hdomU : liftPair A B u (p.val.1 ∪' funInputUnion B C t') ∈
        (productSystem A B).Con :=
      ProdCon_liftPair A B hu hinU
    have h1 : h.rel (liftPair A B u (p.val.1 ∪' funInputUnion B C t')) p.val.2 :=
      h.mono hp
        (entSet_liftPair A B hu hinU (proposition_2_3_iii A hu) hEnt_p)
        (proposition_2_3_iii C (h.rel_cod hp)) hdomU (h.rel_cod hp)
    have h2 : h.rel (liftPair A B u (p.val.1 ∪' funInputUnion B C t'))
        (funOutputUnion B C t') :=
      h.mono ih'
        (entSet_liftPair A B hu hinU (proposition_2_3_iii A hu) hEnt_t)
        (proposition_2_3_iii C (h.rel_cod ih')) hdomU (h.rel_cod ih')
    rw [funInputUnion_insert, funOutputUnion_insert]
    exact h.union_right h1 h2

end InfoSys

end DomainTheory.InformationSystems
