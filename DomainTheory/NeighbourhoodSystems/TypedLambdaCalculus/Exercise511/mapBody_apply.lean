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

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise511

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*} (V : NeighborhoodSystem α)


theorem mapBody_apply (W : (funSpace (Arg V) (iterSys V)).Element)
    (s : (iterSys (funSpace V V)).Element) (x : V.Element) :
    (mapBody V).toElementMap (pair W (pair s x)) =
      (push V).toElementMap
        (pair ((toApproxMap ((head (funSpace V V)).toElementMap s)).toElementMap x)
          ((toApproxMap W).toElementMap (pair ((tail (funSpace V V)).toElementMap s) x))) := by
  rw [mapBody, toElementMap_comp]
  simp only [toElementMap_paired, toElementMap_comp, toElementMap_proj₀, toElementMap_proj₁,
    fst_pair, snd_pair, evalMap_apply]

end DomainTheory.NeighbourhoodSystems.Exercise511
