module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise512.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise512.Wop_apply

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.toElementMap_fixElement
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise512

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond TD)

variable {α : Type*} (V : NeighborhoodSystem α)
  (p : ApproximableMap V TD) (f : ApproximableMap V V)


/-- **Exercise 5.12 (Scott 1981, PRG-19).** The defining recursion of the `while`-loop:
`w(x) = cond(p(x), w(f(x)), x)`. -/
theorem whileMap_rec (x : V.Element) :
    (whileMap V p f).toElementMap x =
      (cond V).toElementMap
        (pair (p.toElementMap x)
          (pair ((whileMap V p f).toElementMap (f.toElementMap x)) x)) := by
  have hfix : (Wop V p f).toElementMap (whileFix V p f) = whileFix V p f :=
    toElementMap_fixElement (Wop V p f)
  have := Wop_apply V p f (whileFix V p f) x
  rw [hfix] at this
  exact this

end DomainTheory.NeighbourhoodSystems.Exercise512
