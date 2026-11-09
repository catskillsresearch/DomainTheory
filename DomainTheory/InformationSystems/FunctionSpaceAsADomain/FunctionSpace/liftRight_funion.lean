module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.liftRight

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

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
    rcases (liftRight.mem A B).1 hp with ⟨y, hy, rfl⟩
    rcases funion.mem.mp hy with hy | hy
    · exact funion.mem.mpr (Or.inl ((liftRight.mem A B).2 ⟨y, hy, rfl⟩))
    · exact funion.mem.mpr (Or.inr ((liftRight.mem A B).2 ⟨y, hy, rfl⟩))
  · intro hp
    rcases funion.mem.mp hp with hp | hp
    · rcases (liftRight.mem A B).1 hp with ⟨y, hy, rfl⟩
      exact (liftRight.mem A B).2 ⟨y, funion.mem.mpr (Or.inl hy), rfl⟩
    · rcases (liftRight.mem A B).1 hp with ⟨y, hy, rfl⟩
      exact (liftRight.mem A B).2 ⟨y, funion.mem.mpr (Or.inr hy), rfl⟩

end InfoSys
end DomainTheory.InformationSystems
