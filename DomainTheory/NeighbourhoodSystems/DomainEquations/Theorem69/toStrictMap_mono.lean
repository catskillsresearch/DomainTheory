module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition68
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe u

variable {α β γ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- `toStrictMap` is monotone. -/
theorem toStrictMap_mono {φ φ' : (strictFun V₀ V₁).Element} (h : φ ≤ φ') :
    toStrictMap φ ≤ toStrictMap φ' := by
  intro X Y hrel
  rw [toStrictMap_rel] at hrel ⊢
  exact h _ hrel

end DomainTheory.NeighbourhoodSystems
