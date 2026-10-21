/-ai
The right lift of a choice-free union equals the choice-free union of the right lifts.

Extensionality is used. A right-lifted token of the union comes from one summand and is reassembled as a member of the corresponding lifted union. A token of the union of the lifts is a right lift from one summand, and that membership is reassembled as membership in the union before lifting.
ai-/
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
