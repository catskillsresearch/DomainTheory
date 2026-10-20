module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.predSet_union
public import DomainTheory.DataTypesAsLattices.Closures.predSet_succSet
public import DomainTheory.DataTypesAsLattices.Closures.boxShift_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices































theorem boxShift_isRetract {a : Pomega} (ha : IsRetract a) :
    IsRetract (boxShift a) := by
  change boxShift a =
    graph (fun x => funOf (boxShift a) (funOf (boxShift a) x))
  apply graph_ext
  intro x
  rw [boxShift_app, boxShift_app]
  have hpred : predSet (ofNat 0 ∪ succSet (funOf a (predSet x))) =
      funOf a (predSet x) := by
    rw [predSet_union, predSet_ofNat_zero, predSet_succSet]
    simp [botElem]
  rw [hpred, retract_app ha]

end DomainTheory.DataTypesAsLattices
