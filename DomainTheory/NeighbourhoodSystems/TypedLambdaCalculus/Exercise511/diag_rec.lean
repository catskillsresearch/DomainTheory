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

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.fixMap_fixed
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise511

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*} (V : NeighborhoodSystem α)


/-- **Exercise 5.11 (Scott 1981, PRG-19).** The recursion `diag(x) = push(x, diag(x))`. -/
theorem diag_rec (x : V.Element) :
    (diag V).toElementMap x =
      (push V).toElementMap (pair x ((diag V).toElementMap x)) := by
  rw [diag, toElementMap_comp]
  set φ := (curry (push V)).toElementMap x with hφ
  have hfix := fixMap_fixed (iterSys V) φ
  have hval := toElementMap_curry_apply (push V) x ((fixMap (iterSys V)).toElementMap φ)
  rw [← hφ] at hval
  rw [hval] at hfix
  exact hfix.symm

end DomainTheory.NeighbourhoodSystems.Exercise511
