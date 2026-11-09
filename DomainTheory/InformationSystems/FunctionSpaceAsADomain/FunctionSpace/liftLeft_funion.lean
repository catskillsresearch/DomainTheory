module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.liftLeft

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
    rcases (liftLeft.mem A B).1 hp with ⟨x, hx, rfl⟩
    rcases funion.mem.mp hx with hx | hx
    · exact funion.mem.mpr (Or.inl ((liftLeft.mem A B).2 ⟨x, hx, rfl⟩))
    · exact funion.mem.mpr (Or.inr ((liftLeft.mem A B).2 ⟨x, hx, rfl⟩))
  · intro hp
    rcases funion.mem.mp hp with hp | hp
    · rcases (liftLeft.mem A B).1 hp with ⟨x, hx, rfl⟩
      exact (liftLeft.mem A B).2 ⟨x, funion.mem.mpr (Or.inl hx), rfl⟩
    · rcases (liftLeft.mem A B).1 hp with ⟨x, hx, rfl⟩
      exact (liftLeft.mem A B).2 ⟨x, funion.mem.mpr (Or.inr hx), rfl⟩

end InfoSys
end DomainTheory.InformationSystems
