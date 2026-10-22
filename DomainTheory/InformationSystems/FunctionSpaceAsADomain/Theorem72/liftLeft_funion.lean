module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid32
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

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
