module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus_map_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem boxPlus_app (a b u : Pomega) :
    funOf (boxPlus a b) u =
      dcondSet (boxTag 0 (squareFst u) ∪ boxTag 1 (squareSnd u))
        (squarePair (funOf (boxShift a) (squareFst u)) botElem)
        (squarePair botElem (funOf (boxShift b) (squareSnd u))) :=
  beta (boxPlus_map_isScottContinuous a b) u

end DomainTheory.DataTypesAsLattices
