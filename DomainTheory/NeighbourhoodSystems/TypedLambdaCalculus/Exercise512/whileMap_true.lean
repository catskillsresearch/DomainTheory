/-ai
If the test holds at x, so that p(x) is true, then the while-loop at x equals the loop at f(x).

Rewrite the loop by its recursion equation, substitute the hypothesis that the test is true, and apply the conditional law for true.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise512.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise512.whileMap_rec

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise512

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond TD)

variable {α : Type*} (V : NeighborhoodSystem α)
  (p : ApproximableMap V TD) (f : ApproximableMap V V)


/-- If the test holds (`p(x) = true`), the loop runs the body: `w(x) = w(f(x))`. -/
theorem whileMap_true {x : V.Element} (hx : p.toElementMap x = Example23.trueElt) :
    (whileMap V p f).toElementMap x = (whileMap V p f).toElementMap (f.toElementMap x) := by
  rw [whileMap_rec, hx, Exercise326.cond_true]

end DomainTheory.NeighbourhoodSystems.Exercise512
