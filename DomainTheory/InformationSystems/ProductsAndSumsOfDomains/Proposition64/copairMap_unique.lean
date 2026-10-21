/-ai
An approximable map h from the separated sum to C that composes with the left injection to give f, composes with the right injection to give g, and sends the bottom element to the bottom element of C, equals the copairing of f and g. This is the uniqueness clause of Scott's Proposition 6.4.

Extensionality is checked in both directions. If h relates a sum-consistent set u to a consistent set s, the emptiness dichotomy for the left projection splits the argument. When both projections are empty, the bottom-like relation yields empty entailment in C. When the left projection is empty and the right projection contains a token, monotonicity of h along the one-sided right entailment relates the right lift of that projection to s, so the composite hypothesis gives the relation for g and the right branch of copairing applies. When the left projection contains a token, sum consistency forces the right projection to be empty, and the same argument with the left lift gives the relation for f. Conversely, the empty-entailment alternative follows by monotonicity of h from the empty relation. A left alternative unpacks the composite hypothesis as a witness related by the left injection, and the left-witness entailment together with monotonicity of h transfers the relation. A right alternative is the same argument with the right injection and the right-witness entailment.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.Basic
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.SumCon_liftSumLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.SumCon_liftSumRight
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.lftFinset_eq_empty_or_mem
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.rhtFinset_eq_empty_or_mem
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.entSet_liftLft_of_left_only
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.entSet_liftRht_of_right_only
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.entSet_empty_of_rel_bot_like
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.entSet_u_of_inl_witness
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.entSet_u_of_inr_witness

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β)

namespace ApproximableMap

variable {C : InfoSys γ}


/-- Uniqueness of copairing (Scott Prop 6.4). -/
theorem copairMap_unique (f : ApproximableMap A C) (g : ApproximableMap B C)
    (h : ApproximableMap (sumSystem A B) C)
    (hinl : comp h (inlMap A B) = f) (hinr : comp h (inrMap A B) = g)
    (hbot : h.toElement (sumSystem A B).botElement = C.botElement) :
    h = copairMap A B f g := by
  refine ApproximableMap.ext fun u s => ?_
  constructor
  · intro hh
    have hu : SumCon A B u := h.rel_dom hh
    have hs : s ∈ C.Con := h.rel_cod hh
    refine ⟨hu, hs, ?_⟩
    rcases lftFinset_eq_empty_or_mem u with hl | ⟨x0, hx0⟩
    · rcases rhtFinset_eq_empty_or_mem u with hr | ⟨y0, hy0⟩
      · exact Or.inl (entSet_empty_of_rel_bot_like A B h hbot hu hs hl hr hh)
      · have hl' : lftFinset u = ∅ := hl
        have hg : g.rel (rhtFinset u) s := by
          have hinr' : (comp h (inrMap A B)).rel (rhtFinset u) s := by
            refine ⟨liftSumRight (α := α) (rhtFinset u), ?_, ?_⟩
            · exact ⟨rht_mem_Con_of_SumCon_lft_empty A B hu hl',
                SumCon_liftSumRight A B (rht_mem_Con_of_SumCon_lft_empty A B hu hl'),
                lftFinset_liftSumRight (α := α) _, by
                  rw [rhtFinset_liftSumRight]
                  exact proposition_2_3_iii B
                    (rht_mem_Con_of_SumCon_lft_empty A B hu hl')⟩
            · exact h.mono hh (entSet_liftRht_of_right_only A B hu hl')
                (proposition_2_3_iii C hs)
                (SumCon_liftSumRight A B (rht_mem_Con_of_SumCon_lft_empty A B hu hl')) hs
          simpa [hinr] using hinr'
        exact Or.inr (Or.inr ⟨Finset.ne_empty_of_mem hy0, hg⟩)
    · have hne : lftFinset u ≠ ∅ := Finset.ne_empty_of_mem hx0
      have hr : rhtFinset u = ∅ := SumCon_rht_empty_of_lft_nonempty A B hu hne
      have hf : f.rel (lftFinset u) s := by
        have hinl' : (comp h (inlMap A B)).rel (lftFinset u) s := by
          refine ⟨liftSumLeft (β := β) (lftFinset u), ?_, ?_⟩
          · exact ⟨lft_mem_Con_of_SumCon_rht_empty A B hu hr,
              SumCon_liftSumLeft A B (lft_mem_Con_of_SumCon_rht_empty A B hu hr),
              rhtFinset_liftSumLeft (β := β) _, by
                rw [lftFinset_liftSumLeft]
                exact proposition_2_3_iii A
                  (lft_mem_Con_of_SumCon_rht_empty A B hu hr)⟩
          · exact h.mono hh (entSet_liftLft_of_left_only A B hu hr)
              (proposition_2_3_iii C hs)
              (SumCon_liftSumLeft A B (lft_mem_Con_of_SumCon_rht_empty A B hu hr)) hs
        simpa [hinl] using hinl'
      exact Or.inr (Or.inl ⟨hne, hf⟩)
  · intro hc
    rcases hc with ⟨hu, hs, hcop⟩
    rcases hcop with hE | ⟨hne, hf⟩ | ⟨hne, hg⟩
    · have hb : h.rel ∅ s :=
        h.mono h.empty_rel ((sumSystem A B).entSet_empty _) hE
          (sumSystem A B).con_empty hs
      exact h.mono hb ((sumSystem A B).entSet_empty _) (proposition_2_3_iii C hs) hu hs
    · have : (comp h (inlMap A B)).rel (lftFinset u) s := by simpa [hinl] using hf
      rcases this with ⟨u', hinl', hh'⟩
      have hr : rhtFinset u = ∅ := SumCon_rht_empty_of_lft_nonempty A B hu hne
      have hEnt : (sumSystem A B).EntSet u u' :=
        entSet_u_of_inl_witness A B hne hinl'
          (proposition_2_3_iii A (lft_mem_Con_of_SumCon_rht_empty A B hu hr)) hu hr
      exact h.mono hh' hEnt (proposition_2_3_iii C hs) hu hs
    · have : (comp h (inrMap A B)).rel (rhtFinset u) s := by simpa [hinr] using hg
      rcases this with ⟨u', hinr', hh'⟩
      have hl : lftFinset u = ∅ := SumCon_lft_empty_of_rht_nonempty A B hu hne
      have hEnt : (sumSystem A B).EntSet u u' :=
        entSet_u_of_inr_witness A B hne hinr'
          (proposition_2_3_iii B (rht_mem_Con_of_SumCon_lft_empty A B hu hl)) hu hl
      exact h.mono hh' hEnt (proposition_2_3_iii C hs) hu hs

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
