module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.strictId
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.strictProj₀
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.qSel
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.kSel
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.argX
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.argY
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.primBody
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.primOp
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.primRec
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.muBody
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.muOp
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.muRec
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.muMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.primBody_apply

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Theorem56

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN constLiftN_natElem)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)


section PrimRec

variable (f : ApproximableMap N N) (g : ApproximableMap (prod N (prod N N)) N)


/-- The defining recursion of `primRec`. -/
theorem primRec_rec (x y : N.Element) :
    (primRec f g).toElementMap (pair x y) =
      (cond N).toElementMap
        (pair (zeroMap.toElementMap x)
          (pair (f.toElementMap y)
            (g.toElementMap
              (pair (predMap.toElementMap x)
                (pair y ((primRec f g).toElementMap
                  (pair (predMap.toElementMap x) y))))))) := by
  have hfix : (primOp f g).toElementMap (primOp f g).fixElement = (primOp f g).fixElement :=
    toElementMap_fixElement (primOp f g)
  have hval := toElementMap_curry_apply (primBody f g) (primOp f g).fixElement (pair x y)
  rw [← primOp, hfix] at hval
  rw [primRec, hval, primBody_apply]

end PrimRec
end DomainTheory.NeighbourhoodSystems.Theorem56
