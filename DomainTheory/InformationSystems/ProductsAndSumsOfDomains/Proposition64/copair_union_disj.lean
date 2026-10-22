module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.instLeftCommutativeLiftSumLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.instLeftCommutativeLiftSumRight

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β)

namespace ApproximableMap

variable {C : InfoSys γ}

theorem copair_union_disj (f : ApproximableMap A C) (g : ApproximableMap B C)
    {u : Finset (SumToken α β)} {s s' : Finset γ}
    (hu : SumCon A B u) (hs : s ∈ C.Con) (hs' : s' ∈ C.Con)
    (h : C.EntSet ∅ s ∨ (lftFinset u ≠ ∅ ∧ f.rel (lftFinset u) s) ∨
      (rhtFinset u ≠ ∅ ∧ g.rel (rhtFinset u) s))
    (h' : C.EntSet ∅ s' ∨ (lftFinset u ≠ ∅ ∧ f.rel (lftFinset u) s') ∨
      (rhtFinset u ≠ ∅ ∧ g.rel (rhtFinset u) s')) :
    C.EntSet ∅ (s ∪' s') ∨
      (lftFinset u ≠ ∅ ∧ f.rel (lftFinset u) (s ∪' s')) ∨
        (rhtFinset u ≠ ∅ ∧ g.rel (rhtFinset u) (s ∪' s')) := by
  rcases h with h | ⟨hne, hf⟩ | ⟨hne, hg⟩ <;> rcases h' with h' | ⟨hne', hf'⟩ | ⟨hne', hg'⟩
  · exact Or.inl (proposition_2_3_vi (sys := C) h h')
  · have hf0 : f.rel (lftFinset u) s :=
      f.mono f.empty_rel (A.entSet_empty _) h
        (SumCon_lft_con_of_lft_nonempty A B hu hne') hs
    exact Or.inr (Or.inl ⟨hne', f.union_right hf0 hf'⟩)
  · have hg0 : g.rel (rhtFinset u) s :=
      g.mono g.empty_rel (B.entSet_empty _) h
        (SumCon_rht_con_of_rht_nonempty A B hu hne') hs
    exact Or.inr (Or.inr ⟨hne', g.union_right hg0 hg'⟩)
  · have hf0 : f.rel (lftFinset u) s' :=
      f.mono f.empty_rel (A.entSet_empty _) h'
        (SumCon_lft_con_of_lft_nonempty A B hu hne) hs'
    exact Or.inr (Or.inl ⟨hne, f.union_right hf hf0⟩)
  · exact Or.inr (Or.inl ⟨hne, f.union_right hf hf'⟩)
  · exact False.elim (hne' (SumCon_rht_empty_of_lft_nonempty A B hu hne))
  · have hg0 : g.rel (rhtFinset u) s' :=
      g.mono g.empty_rel (B.entSet_empty _) h'
        (SumCon_rht_con_of_rht_nonempty A B hu hne) hs'
    exact Or.inr (Or.inr ⟨hne, g.union_right hg hg0⟩)
  · exact False.elim (hne' (SumCon_lft_empty_of_rht_nonempty A B hu hne))
  · exact Or.inr (Or.inr ⟨hne, g.union_right hg hg'⟩)

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
