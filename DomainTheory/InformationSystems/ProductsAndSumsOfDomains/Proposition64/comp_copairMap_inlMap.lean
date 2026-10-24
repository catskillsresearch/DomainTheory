module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.liftSumLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.liftSumRight
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.inlMap
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.inrMap
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.copairMap
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.sumLftCarrier
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.sumRhtCarrier
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.sumElementLft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.sumElementRht
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.instLeftCommutativeLiftSumLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.instLeftCommutativeLiftSumRight
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.mem_foldr_liftSumLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.mem_foldr_liftSumRight
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.mem_liftSumLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.mem_liftSumRight
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.lftFinset_liftSumLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.rhtFinset_liftSumLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.rhtFinset_liftSumRight
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.lftFinset_liftSumRight
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.rht_eq_empty_of_sumEntSet
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.lft_eq_empty_of_sumEntSet
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.entSet_lft_of_sumEntSet
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.entSet_rht_of_sumEntSet
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.lft_mem_Con_of_SumCon_rht_empty
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.rht_mem_Con_of_SumCon_lft_empty
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.copair_union_disj
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.SumCon_liftSumLeft

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β)

namespace ApproximableMap

variable {C : InfoSys γ}


theorem comp_copairMap_inlMap (f : ApproximableMap A C) (g : ApproximableMap B C) :
    comp (copairMap A B f g) (inlMap A B) = f := by
  refine ApproximableMap.ext fun v s => ?_
  constructor
  · rintro ⟨u, ⟨hv, hu, hr, hEnt⟩, ⟨_, hs, hcop⟩⟩
    rcases hcop with hE | ⟨_, hf⟩ | ⟨hne, _⟩
    · exact f.mono f.empty_rel (A.entSet_empty v) hE hv hs
    · exact f.mono hf hEnt (proposition_2_3_iii C hs) hv hs
    · exact False.elim (hne hr)
  · intro hf
    -- Always lift `insert Δ v` so the left branch of copair is nonempty (avoids
    -- classical `by_cases` on `v = ∅`).
    let vBot := insert A.bot v
    have hvBot : vBot ∈ A.Con := A.ent_con (A.ent_bot (f.rel_dom hf))
    have hEntBot : A.EntSet vBot v :=
      fun _ hx => A.ent_refl hvBot (Finset.mem_insert_of_mem hx)
    have hfBot : f.rel vBot s :=
      f.mono hf hEntBot (proposition_2_3_iii C (f.rel_cod hf)) hvBot (f.rel_cod hf)
    refine ⟨liftSumLeft (β := β) vBot, ?_, ?_⟩
    · refine ⟨f.rel_dom hf, SumCon_liftSumLeft A B hvBot,
        rhtFinset_liftSumLeft (β := β) vBot, ?_⟩
      rw [lftFinset_liftSumLeft]
      intro x hx
      rcases Finset.mem_insert.mp hx with hx | hx
      · subst hx; exact A.ent_bot (f.rel_dom hf)
      · exact A.ent_refl (f.rel_dom hf) hx
    · refine ⟨SumCon_liftSumLeft A B hvBot, f.rel_cod hf, Or.inr (Or.inl ⟨?_, ?_⟩)⟩
      · rw [lftFinset_liftSumLeft]; exact Finset.insert_ne_empty A.bot v
      · rw [lftFinset_liftSumLeft]; exact hfBot

end ApproximableMap
end InfoSys

end DomainTheory.InformationSystems
