/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.FunctionSpace
import DomainTheory.InformationSystems.Proposition53
import DomainTheory.InformationSystems.Proposition55
import DomainTheory.InformationSystems.Proposition62
import DomainTheory.InformationSystems.Factoid32
import DomainTheory.InformationSystems.Theorem72.Basic


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)






open ApproximableMap














theorem liftRight_funion (v v' : Finset β) :
    liftRight A B (v ∪' v') = liftRight A B v ∪' liftRight A B v' := by
  ext p
  constructor
  · intro hp
    rcases (mem_liftRight A B).1 hp with ⟨y, hy, rfl⟩
    rcases mem_funion.mp hy with hy | hy
    · exact mem_funion.mpr (Or.inl ((mem_liftRight A B).2 ⟨y, hy, rfl⟩))
    · exact mem_funion.mpr (Or.inr ((mem_liftRight A B).2 ⟨y, hy, rfl⟩))
  · intro hp
    rcases mem_funion.mp hp with hp | hp
    · rcases (mem_liftRight A B).1 hp with ⟨y, hy, rfl⟩
      exact (mem_liftRight A B).2 ⟨y, mem_funion.mpr (Or.inl hy), rfl⟩
    · rcases (mem_liftRight A B).1 hp with ⟨y, hy, rfl⟩
      exact (mem_liftRight A B).2 ⟨y, mem_funion.mpr (Or.inr hy), rfl⟩

end InfoSys
end DomainTheory.InformationSystems
