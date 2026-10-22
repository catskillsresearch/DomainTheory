/-ai
If a and b are retracts, their boxed product is a retract.

The retract equation is equality with the graph of double application. Graph extensionality and two unfoldings of the product reduce the coordinates by the square-projection equations, and the retract equations for a and b remove the second applications.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_9
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_10
public import DomainTheory.DataTypesAsLattices.Closures.boxTensor_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem boxTensor_isRetract {a b : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    IsRetract (boxTensor a b) := by
  change boxTensor a b =
    graph (fun u => funOf (boxTensor a b) (funOf (boxTensor a b) u))
  apply graph_ext
  intro u
  rw [boxTensor_app, boxTensor_app, eq_5_9, eq_5_10, retract_app ha, retract_app hb]

end DomainTheory.DataTypesAsLattices
