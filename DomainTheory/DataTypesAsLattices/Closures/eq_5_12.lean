/-ai
Scott 1976, (5.12). The boxed product of a and b unfolds as the graph of the map sending u to the square pair of a applied to the first square component and b applied to the second.

The equality is the definition.
ai-/
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
