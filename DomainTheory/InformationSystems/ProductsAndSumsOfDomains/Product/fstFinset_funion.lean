/-ai
The left projection preserves constructive union.

A token witnessing membership in the projection of a constructive union lies in one summand, and the same token witnesses membership in the corresponding projected summand. Conversely, a witness in either projected summand is a token of that summand, hence of the union, and it still has least second component.
ai-/
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
