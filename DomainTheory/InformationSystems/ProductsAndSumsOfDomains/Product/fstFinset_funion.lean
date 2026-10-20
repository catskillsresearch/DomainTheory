/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]





variable (A : InfoSys α) (B : InfoSys β)




















theorem fstFinset_funion (u v : Finset (ProdToken A B)) :
    fstFinset A B (u ∪' v) = fstFinset A B u ∪' fstFinset A B v := by
  ext x
  constructor
  · intro hx
    rcases (mem_fstFinset A B).1 hx with ⟨p, hp, hbot, hx'⟩
    rcases mem_funion.mp hp with hp | hp
    · exact mem_funion.mpr (Or.inl ((mem_fstFinset A B).2 ⟨p, hp, hbot, hx'⟩))
    · exact mem_funion.mpr (Or.inr ((mem_fstFinset A B).2 ⟨p, hp, hbot, hx'⟩))
  · intro hx
    rcases mem_funion.mp hx with hx | hx
    · rcases (mem_fstFinset A B).1 hx with ⟨p, hp, hbot, hx'⟩
      exact (mem_fstFinset A B).2 ⟨p, mem_funion.mpr (Or.inl hp), hbot, hx'⟩
    · rcases (mem_fstFinset A B).1 hx with ⟨p, hp, hbot, hx'⟩
      exact (mem_fstFinset A B).2 ⟨p, mem_funion.mpr (Or.inr hp), hbot, hx'⟩

end InfoSys
end DomainTheory.InformationSystems
