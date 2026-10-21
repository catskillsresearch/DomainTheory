/-ai
The copairing of Proposition 6.4 sends approximable maps f from A to C and g from B to C to the approximable map from the separated sum to C that relates a sum-consistent set u to a consistent set s when C entails s from the empty set, or the left projection of u is nonempty and f relates that projection to s, or the right projection of u is nonempty and g relates that projection to s. The domain and codomain of a related pair are the two consistency hypotheses. The empty relation holds because the empty sum set is consistent, the empty set of C is consistent, and C entails the empty set from the empty set. Closure under union on the right is the disjoint union lemma for the three alternatives, and consistency of the union is the subset axiom applied to proposition 2.3(ii) in the empty-entailment case and the codomain of f or of g in the other cases. Monotonicity preserves the empty-entailment alternative by proposition 2.3(iv), and preserves a left or right alternative because sum entailment keeps that projection nonempty and the corresponding map is monotone along the projected entailment, with consistency of the projected set given by the nonempty-side lemma.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.instLeftCommutativeLiftSumLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.instLeftCommutativeLiftSumRight
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.entSet_lft_of_sumEntSet
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.entSet_rht_of_sumEntSet
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.copair_union_disj

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β)

set_option linter.unusedSectionVars false

namespace ApproximableMap

variable {C : InfoSys γ}

/-- **Proposition 6.4(3).** Copairing of approximable maps. -/
def copairMap (f : ApproximableMap A C) (g : ApproximableMap B C) :
    ApproximableMap (sumSystem A B) C where
  rel u s :=
    SumCon A B u ∧ s ∈ C.Con ∧
      (C.EntSet ∅ s ∨
        (lftFinset u ≠ ∅ ∧ f.rel (lftFinset u) s) ∨
          (rhtFinset u ≠ ∅ ∧ g.rel (rhtFinset u) s))
  rel_dom h := h.1
  rel_cod h := h.2.1
  empty_rel := ⟨SumCon_empty A B, C.con_empty, Or.inl (C.entSet_empty ∅)⟩
  union_right := by
    rintro u s s' ⟨hu, hs, h⟩ ⟨_, hs', h'⟩
    have hU := copair_union_disj A B f g hu hs hs' h h'
    refine ⟨hu, ?_, hU⟩
    rcases hU with hE | ⟨_, hf⟩ | ⟨_, hg⟩
    · exact C.con_subset (proposition_2_3_ii (sys := C) C.con_empty hE)
        (subset_funion_right _ _)
    · exact f.rel_cod hf
    · exact g.rel_cod hg
  mono := by
    rintro u u' s s' ⟨hu, hs, h⟩ hEntu hEnts hu' hs'
    refine ⟨hu', hs', ?_⟩
    rcases h with h | ⟨hne, hf⟩ | ⟨hne, hg⟩
    · exact Or.inl (proposition_2_3_iv (sys := C) C.con_empty hs h hEnts)
    · have hne' : lftFinset u' ≠ ∅ := by
        obtain ⟨x, hx⟩ := Finset.nonempty_of_ne_empty hne
        exact (hEntu _ ((mem_lftFinset).1 hx)).2.1
      exact Or.inr (Or.inl ⟨hne',
        f.mono hf (entSet_lft_of_sumEntSet A B hEntu) hEnts
          (SumCon_lft_con_of_lft_nonempty A B hu' hne') hs'⟩)
    · have hne' : rhtFinset u' ≠ ∅ := by
        obtain ⟨y, hy⟩ := Finset.nonempty_of_ne_empty hne
        exact (hEntu _ ((mem_rhtFinset).1 hy)).2.1
      exact Or.inr (Or.inr ⟨hne',
        g.mono hg (entSet_rht_of_sumEntSet A B hEntu) hEnts
          (SumCon_rht_con_of_rht_nonempty A B hu' hne') hs'⟩)

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
