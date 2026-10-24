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
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.muRec_rec

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.cond_false
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Theorem56

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN constLiftN_natElem)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)


section Mu

variable (f : ApproximableMap (prod N N) N)


/-- **μ, step.** If `f(n̂, m̂)` is a positive total `(j+1)^`, the search advances to `n+1`. -/
theorem muRec_step {n m j : ℕ}
    (h : f.toElementMap (pair (natElem n) (natElem m)) = natElem (j + 1)) :
    (muRec f).toElementMap (pair (natElem n) (natElem m)) =
      (muRec f).toElementMap (pair (natElem (n + 1)) (natElem m)) := by
  rw [muRec_rec, h, zeroMap_natElem_succ, Exercise326.cond_false, succMap_natElem]

end Mu
end DomainTheory.NeighbourhoodSystems.Theorem56
