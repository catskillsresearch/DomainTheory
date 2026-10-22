module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (5.13).** Unfolding of the boxed sum. -/
theorem eq_5_13 (a b : Pomega) :
    boxPlus a b = graph (fun u =>
      dcondSet (condSet (squareFst u) (ofNat 0) (ofNat 0) ∪
          condSet (squareSnd u) (ofNat 1) (ofNat 1))
        (squarePair (funOf (boxShift a) (squareFst u)) botElem)
        (squarePair botElem (funOf (boxShift b) (squareSnd u)))) :=
  rfl

end DomainTheory.DataTypesAsLattices
