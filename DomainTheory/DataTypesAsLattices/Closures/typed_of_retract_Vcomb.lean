/-ai
A point typed by a set remains typed by the universe combinator applied to that set.

After the application law for the universe combinator, typing is equality of the point with the application of the graph of the universe operator. The beta law rewrites that application as the value of the operator. The point is contained in that value by the expansive inclusion. Conversely, every member of the value belongs to the point: the point contains itself, and the original typing equation makes the set applied to the point contained in the point, so the point is one of the sets in the intersection that defines the operator.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_16
public import DomainTheory.DataTypesAsLattices.Closures.Vapply_right_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Closures.Vcomb_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- `V` does not change already-closed points of a retract. -/
theorem typed_of_retract_Vcomb {a x : Pomega} (hx : typed x a) :
    typed x (funOf Vcomb a) := by
  rw [typed, Vcomb_app]
  have happ : funOf (graph (fun z => Vapply a z)) x = Vapply a x :=
    beta (Vapply_right_isScottContinuous a) x
  rw [happ]
  apply subset_antisymm
  · exact eq_5_16 a x
  · intro k hk
    exact hk x ⟨subset_rfl, by rw [← hx]⟩


end DomainTheory.DataTypesAsLattices
