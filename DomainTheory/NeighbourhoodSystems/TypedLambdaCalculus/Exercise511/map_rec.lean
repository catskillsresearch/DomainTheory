module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.unfold
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.fold
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.head
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.tail
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.push
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.diag
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.mapBody
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.mapOp
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.mapMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.iterProdIso_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.head_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.tail_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.Arg
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.mapBody_apply

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.toElementMap_fixElement
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise511

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*} (V : NeighborhoodSystem α)


/-- **Exercise 5.11 (Scott 1981, PRG-19).** The recursion defining `map`:
`map(s, x) = push((head s)(x), map(tail s, x))`. -/
theorem map_rec (s : (iterSys (funSpace V V)).Element) (x : V.Element) :
    (mapMap V).toElementMap (pair s x) =
      (push V).toElementMap
        (pair ((toApproxMap ((head (funSpace V V)).toElementMap s)).toElementMap x)
          ((mapMap V).toElementMap (pair ((tail (funSpace V V)).toElementMap s) x))) := by
  have hfix : (mapOp V).toElementMap (mapOp V).fixElement = (mapOp V).fixElement :=
    toElementMap_fixElement (mapOp V)
  have hval := toElementMap_curry_apply (mapBody V) (mapOp V).fixElement (pair s x)
  rw [← mapOp, hfix] at hval
  rw [mapMap, hval, mapBody_apply]

end DomainTheory.NeighbourhoodSystems.Exercise511
