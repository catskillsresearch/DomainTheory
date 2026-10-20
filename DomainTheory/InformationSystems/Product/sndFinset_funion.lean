/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Constructive
import DomainTheory.InformationSystems.Proposition23
import DomainTheory.InformationSystems.Product.Basic


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]





variable (A : InfoSys α) (B : InfoSys β)




















theorem sndFinset_funion (u v : Finset (ProdToken A B)) :
    sndFinset A B (u ∪' v) = sndFinset A B u ∪' sndFinset A B v := by
  ext y
  constructor
  · intro hy
    rcases (mem_sndFinset A B).1 hy with ⟨p, hp, hbot, hy'⟩
    rcases mem_funion.mp hp with hp | hp
    · exact mem_funion.mpr (Or.inl ((mem_sndFinset A B).2 ⟨p, hp, hbot, hy'⟩))
    · exact mem_funion.mpr (Or.inr ((mem_sndFinset A B).2 ⟨p, hp, hbot, hy'⟩))
  · intro hy
    rcases mem_funion.mp hy with hy | hy
    · rcases (mem_sndFinset A B).1 hy with ⟨p, hp, hbot, hy'⟩
      exact (mem_sndFinset A B).2 ⟨p, mem_funion.mpr (Or.inl hp), hbot, hy'⟩
    · rcases (mem_sndFinset A B).1 hy with ⟨p, hp, hbot, hy'⟩
      exact (mem_sndFinset A B).2 ⟨p, mem_funion.mpr (Or.inr hp), hbot, hy'⟩

end InfoSys
end DomainTheory.InformationSystems
