module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise507

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ} {V₃ : NeighborhoodSystem δ}

/-- **Three-variable abstraction** `λx, y, z. τ`, via nested currying on `(D₀ × D₁) × D₂ → D₃`.
Each `curry` strips one variable, so a function of `n` variables is reached by `n - 1` curryings —
single-variable binders all the way down. -/
def curry₃ (g : ApproximableMap (prod (prod V₀ V₁) V₂) V₃) :
    ApproximableMap V₀ (funSpace V₁ (funSpace V₂ V₃)) :=
  curry (curry g)

end DomainTheory.NeighbourhoodSystems.Exercise507
