module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.Basic
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.condSumEmb_toElementMap

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}




/-- **Exercise 3.26.** `condSum(true, x, y) = in₀(x)`. -/
theorem condSum_true (x : V₀.Element) (y : V₁.Element) :
    (condSum V₀ V₁ h₀ h₁).toElementMap (pair Example23.trueElt (pair x y))
      = (inMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap x := by
  rw [condSum, toElementMap_comp, condSumEmb_toElementMap, cond_true]

end DomainTheory.NeighbourhoodSystems.Exercise326
