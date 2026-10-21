/-ai
If the test fails at x, so that p(x) is false, then the while-loop returns x.

Rewrite the loop by its recursion equation, substitute the hypothesis that the test is false, and apply the conditional law for false.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise512.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise512.whileMap_rec

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.cond_false
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise512

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond TD)

variable {α : Type*} (V : NeighborhoodSystem α)
  (p : ApproximableMap V TD) (f : ApproximableMap V V)


/-- If the test fails (`p(x) = false`), the loop exits: `w(x) = x`. -/
theorem whileMap_false {x : V.Element} (hx : p.toElementMap x = Example23.falseElt) :
    (whileMap V p f).toElementMap x = x := by
  rw [whileMap_rec, hx, Exercise326.cond_false]

end DomainTheory.NeighbourhoodSystems.Exercise512
