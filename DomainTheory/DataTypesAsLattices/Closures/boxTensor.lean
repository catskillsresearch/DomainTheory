/-ai
Scott 1976, (5.12). The product of closures a and b is the graph of the map sending u to the square pair of a applied to the first square component of u and b applied to the second.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.squarePair
public import DomainTheory.DataTypesAsLattices.Closures.squareFst
public import DomainTheory.DataTypesAsLattices.Closures.squareSnd

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (5.12).** Product of closures. -/
def boxTensor (a b : Pomega) : Pomega :=
  graph (fun u => squarePair (funOf a (squareFst u)) (funOf b (squareSnd u)))

end DomainTheory.DataTypesAsLattices
