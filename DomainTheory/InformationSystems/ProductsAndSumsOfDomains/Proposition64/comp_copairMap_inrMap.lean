/-ai
The composite of the copairing of approximable maps f and g with the right injection equals g.

Extensionality reduces the equation to a relation in both directions. A witness of the composite is a sum set related by the right injection and by copairing. The empty-entailment branch of copairing gives the relation for g by monotonicity from the empty relation. The right branch gives it by monotonicity along the recorded entailment, using proposition 2.3(iii) on the codomain. The left branch contradicts emptiness of the left projection in the injection witness. Conversely, if g relates w to s, insert the bottom token of B into w. The enlarged set is consistent by the consistency of the bottom entailment, it entails w by reflexivity on the original members, and monotonicity of g gives the relation on the enlarged set. The right lift of that set witnesses the composite: the left projection of the lift is empty, its right projection equals the enlarged set, whose members are entailed by the bottom entailment or by reflexivity, and copairing takes the right branch because inserting bottom makes that projection nonempty.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.Basic
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.SumCon_liftSumRight

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β)

namespace ApproximableMap

variable {C : InfoSys γ}


theorem comp_copairMap_inrMap (f : ApproximableMap A C) (g : ApproximableMap B C) :
    comp (copairMap A B f g) (inrMap A B) = g := by
  refine ApproximableMap.ext fun w s => ?_
  constructor
  · rintro ⟨u, ⟨hw, hu, hl, hEnt⟩, ⟨_, hs, hcop⟩⟩
    rcases hcop with hE | ⟨hne, _⟩ | ⟨_, hg⟩
    · exact g.mono g.empty_rel (B.entSet_empty w) hE hw hs
    · exact False.elim (hne hl)
    · exact g.mono hg hEnt (proposition_2_3_iii C hs) hw hs
  · intro hg
    let wBot := insert B.bot w
    have hwBot : wBot ∈ B.Con := B.ent_con (B.ent_bot (g.rel_dom hg))
    have hEntBot : B.EntSet wBot w :=
      fun _ hy => B.ent_refl hwBot (Finset.mem_insert_of_mem hy)
    have hgBot : g.rel wBot s :=
      g.mono hg hEntBot (proposition_2_3_iii C (g.rel_cod hg)) hwBot (g.rel_cod hg)
    refine ⟨liftSumRight (α := α) wBot, ?_, ?_⟩
    · refine ⟨g.rel_dom hg, SumCon_liftSumRight A B hwBot,
        lftFinset_liftSumRight (α := α) wBot, ?_⟩
      rw [rhtFinset_liftSumRight]
      intro y hy
      rcases Finset.mem_insert.mp hy with hy | hy
      · subst hy; exact B.ent_bot (g.rel_dom hg)
      · exact B.ent_refl (g.rel_dom hg) hy
    · refine ⟨SumCon_liftSumRight A B hwBot, g.rel_cod hg, Or.inr (Or.inr ⟨?_, ?_⟩)⟩
      · rw [rhtFinset_liftSumRight]; exact Finset.insert_ne_empty B.bot w
      · rw [rhtFinset_liftSumRight]; exact hgBot

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
