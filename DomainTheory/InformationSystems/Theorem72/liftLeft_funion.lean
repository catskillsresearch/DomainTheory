/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.FunctionSpace
public import DomainTheory.InformationSystems.Proposition53
public import DomainTheory.InformationSystems.Proposition55
public import DomainTheory.InformationSystems.Proposition62
public import DomainTheory.InformationSystems.Factoid32
public import DomainTheory.InformationSystems.Theorem72.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)






open ApproximableMap














theorem liftLeft_funion (u u' : Finset α) :
    liftLeft A B (u ∪' u') = liftLeft A B u ∪' liftLeft A B u' := by
  ext p
  constructor
  · intro hp
    rcases (mem_liftLeft A B).1 hp with ⟨x, hx, rfl⟩
    rcases mem_funion.mp hx with hx | hx
    · exact mem_funion.mpr (Or.inl ((mem_liftLeft A B).2 ⟨x, hx, rfl⟩))
    · exact mem_funion.mpr (Or.inr ((mem_liftLeft A B).2 ⟨x, hx, rfl⟩))
  · intro hp
    rcases mem_funion.mp hp with hp | hp
    · rcases (mem_liftLeft A B).1 hp with ⟨x, hx, rfl⟩
      exact (mem_liftLeft A B).2 ⟨x, mem_funion.mpr (Or.inl hx), rfl⟩
    · rcases (mem_liftLeft A B).1 hp with ⟨x, hx, rfl⟩
      exact (mem_liftLeft A B).2 ⟨x, mem_funion.mpr (Or.inr hx), rfl⟩

end InfoSys
end DomainTheory.InformationSystems
