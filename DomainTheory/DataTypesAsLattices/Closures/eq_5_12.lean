module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (5.12).** Unfolding of the boxed product. -/
theorem eq_5_12 (a b : Pomega) :
    boxTensor a b = graph (fun u =>
      squarePair (funOf a (squareFst u)) (funOf b (squareSnd u))) :=
  rfl

end DomainTheory.DataTypesAsLattices
