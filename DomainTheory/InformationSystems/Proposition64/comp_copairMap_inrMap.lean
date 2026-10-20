/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Sum
import DomainTheory.InformationSystems.Factoid33
import DomainTheory.InformationSystems.Proposition53
import DomainTheory.InformationSystems.Proposition55
import DomainTheory.InformationSystems.Proposition64.Basic
import DomainTheory.InformationSystems.Proposition64.SumCon_liftSumRight


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β)

set_option linter.unusedSectionVars false



















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
