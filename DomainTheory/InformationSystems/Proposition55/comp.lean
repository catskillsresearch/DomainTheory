/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Proposition54

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

namespace ApproximableMap

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable {A : InfoSys α} {B : InfoSys β} {C : InfoSys γ}

/-- **Proposition 5.5(i).** Composition of approximable mappings. -/
def comp (g : ApproximableMap B C) (f : ApproximableMap A B) : ApproximableMap A C where
  rel u w := ∃ v, f.rel u v ∧ g.rel v w
  rel_dom := fun ⟨_, hf, _⟩ => f.rel_dom hf
  rel_cod := fun ⟨_, _, hg⟩ => g.rel_cod hg
  empty_rel := ⟨∅, f.empty_rel, g.empty_rel⟩
  union_right := by
    rintro u w w' ⟨v, hf, hg⟩ ⟨v', hf', hg'⟩
    -- Need common middle: use union_right on f to get u f (v ∪' v'), then g.
    have hfU : f.rel u (v ∪' v') := f.union_right hf hf'
    have hvU : v ∪' v' ∈ B.Con := f.rel_cod hfU
    have hEntv : B.EntSet (v ∪' v') v :=
      fun y hy => B.ent_refl hvU (subset_funion_left v v' hy)
    have hEntv' : B.EntSet (v ∪' v') v' :=
      fun y hy => B.ent_refl hvU (subset_funion_right v v' hy)
    have hg1 : g.rel (v ∪' v') w :=
      g.mono hg hEntv (proposition_2_3_iii C (g.rel_cod hg)) hvU (g.rel_cod hg)
    have hg2 : g.rel (v ∪' v') w' :=
      g.mono hg' hEntv' (proposition_2_3_iii C (g.rel_cod hg')) hvU (g.rel_cod hg')
    exact ⟨v ∪' v', hfU, g.union_right hg1 hg2⟩
  mono := by
    rintro u u' w w' ⟨v, hf, hg⟩ hEntu hEntw hu' hw'
    refine ⟨v, ?_, ?_⟩
    · exact f.mono hf hEntu (proposition_2_3_iii B (f.rel_cod hf)) hu' (f.rel_cod hf)
    · exact g.mono hg (proposition_2_3_iii B (f.rel_cod hf)) hEntw (f.rel_cod hf) hw'

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
