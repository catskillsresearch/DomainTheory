module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.inter_ne_master_left

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise510

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem inter_ne_master_right {Y Y' : Set β} (hY : V₁.mem Y) (hYne : Y ≠ V₁.master) :
    Y ∩ Y' ≠ V₁.master :=
  inter_ne_master_left (V₀ := V₁) hY hYne

end DomainTheory.NeighbourhoodSystems.Exercise510
