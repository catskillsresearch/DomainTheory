module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_9
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_10
public import DomainTheory.DataTypesAsLattices.Closures.boxTensor_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem boxTensor_isRetract {a b : Pomega} (ha : Retract a) (hb : Retract b) :
    Retract (boxTensor a b) := by
  constructor
  change boxTensor a b =
    graph (fun u => funOf (boxTensor a b) (funOf (boxTensor a b) u))
  apply graph_ext
  intro u
  rw [boxTensor_app, boxTensor_app, eq_5_9, eq_5_10, retract_app ha, retract_app hb]

end DomainTheory.DataTypesAsLattices
