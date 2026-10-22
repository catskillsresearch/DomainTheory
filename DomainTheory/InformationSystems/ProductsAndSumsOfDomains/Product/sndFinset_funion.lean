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
