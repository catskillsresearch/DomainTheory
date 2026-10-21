/-ai
If a neighbourhood of the second system is other than its master, its intersection with any set is still other than the master.

This is the preceding intersection law applied to the second system.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.inter_ne_master_left

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise510

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem inter_ne_master_right {Y Y' : Set β} (hY : V₁.mem Y) (hYne : Y ≠ V₁.master) :
    Y ∩ Y' ≠ V₁.master :=
  inter_ne_master_left (V₀ := V₁) hY hYne

end DomainTheory.NeighbourhoodSystems.Exercise510
