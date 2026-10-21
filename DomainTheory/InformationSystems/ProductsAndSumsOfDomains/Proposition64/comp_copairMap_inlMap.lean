/-ai
The composite of the copairing of approximable maps f and g with the left injection equals f.

Extensionality reduces the equation to a relation in both directions. A witness of the composite is a sum set related by the left injection and by copairing. The empty-entailment branch of copairing gives the relation for f by monotonicity from the empty relation. The left branch gives it by monotonicity along the recorded entailment, using proposition 2.3(iii) on the codomain. The right branch contradicts emptiness of the right projection in the injection witness. Conversely, if f relates v to s, insert the bottom token of A into v. The enlarged set is consistent by the consistency of the bottom entailment, it entails v by reflexivity on the original members, and monotonicity of f gives the relation on the enlarged set. The left lift of that set witnesses the composite: the right projection of the lift is empty, its left projection equals the enlarged set, whose members are entailed by the bottom entailment or by reflexivity, and copairing takes the left branch because inserting bottom makes that projection nonempty.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.Basic
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.SumCon_liftSumLeft

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β)

set_option linter.unusedSectionVars false



















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
