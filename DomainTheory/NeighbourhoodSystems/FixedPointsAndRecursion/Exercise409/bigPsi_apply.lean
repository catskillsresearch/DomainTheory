/-ai
The elementwise action of Ψ at an operator θ, evaluated at a map f, equals f applied to θ(f).

The definition of Ψ is unfolded, and the currying law, the composition law, the pairing law, the first-projection law, the second component of a pair, and the two evaluation laws rewrite the left side into the right side.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise409.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*}


/-- **Exercise 4.9 (Scott 1981, PRG-19).** The defining equation `Ψ(θ)(f) = f(θ(f))`. -/
theorem bigPsi_apply (V : NeighborhoodSystem α)
    (θ : (funSpace (funSpace V V) V).Element) (f : (funSpace V V).Element) :
    (toApproxMap ((bigPsi V).toElementMap θ)).toElementMap f
      = (toApproxMap f).toElementMap ((toApproxMap θ).toElementMap f) := by
  rw [bigPsi, toElementMap_curry_apply, toElementMap_comp, toElementMap_paired,
    toElementMap_proj₁, snd_pair, evalMap_apply, evalMap_apply]

end DomainTheory.NeighbourhoodSystems
