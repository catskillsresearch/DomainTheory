/-ai
If a is a retract, the shift of a is a retract.

The retract equation is equality with the graph of double application. Graph extensionality and two unfoldings of the shift reduce the claim to the predecessor of the union of the singleton zero with the successor of a applied to the predecessor of x. That predecessor is the application of a, by the predecessor laws for unions, the singleton zero, and successor sets. The retract equation for a then removes the second application.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
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
