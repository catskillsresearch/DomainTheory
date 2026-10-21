/-ai
The sum-valued conditional at bottom returns the bottom of the sum.

Unfold the composite, apply the elementwise computation of the embedding, and use the bottom identity of the conditional.
ai-/
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




/-- **Exercise 3.26.** `condSum(⊥, x, y) = ⊥`. -/
theorem condSum_bot (x : V₀.Element) (y : V₁.Element) :
    (condSum V₀ V₁ h₀ h₁).toElementMap (pair Example23.botElt (pair x y)) = (sum V₀ V₁ h₀ h₁).bot := by
  rw [condSum, toElementMap_comp, condSumEmb_toElementMap, cond_bot]

end DomainTheory.NeighbourhoodSystems.Exercise326
