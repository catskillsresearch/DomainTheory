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





/-- If the test diverges (`p(x) = ⊥`), the loop diverges: `w(x) = ⊥`. -/
theorem whileMap_bot {x : V.Element} (hx : p.toElementMap x = Example23.botElt) :
    (whileMap V p f).toElementMap x = V.bot := by
  rw [whileMap_rec, hx, Exercise326.cond_bot]

end DomainTheory.NeighbourhoodSystems.Exercise512
