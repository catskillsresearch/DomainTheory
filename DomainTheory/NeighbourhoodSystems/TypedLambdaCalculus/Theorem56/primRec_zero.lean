module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.primRec_rec

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Theorem56

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN constLiftN_natElem)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)


section PrimRec

variable (f : ApproximableMap N N) (g : ApproximableMap (prod N (prod N N)) N)


/-- **Primitive recursion, base case.** `h̄(0̂, m̂) = f(m̂)`. -/
theorem primRec_zero (m : ℕ) :
    (primRec f g).toElementMap (pair (natElem 0) (natElem m)) = f.toElementMap (natElem m) := by
  rw [primRec_rec, zeroMap_natElem_zero, Exercise326.cond_true]

end PrimRec
end DomainTheory.NeighbourhoodSystems.Theorem56
