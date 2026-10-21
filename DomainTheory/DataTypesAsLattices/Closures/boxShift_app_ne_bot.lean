/-ai
The application of the shift of a to any set is nonempty.

Zero lies in every such application. An empty application would exclude zero.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.zero_mem_boxShift_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem boxShift_app_ne_bot (a x : Pomega) : funOf (boxShift a) x ≠ botElem := by
  intro h
  have h0 := zero_mem_boxShift_app a x
  rw [h] at h0
  simp [botElem] at h0

end DomainTheory.DataTypesAsLattices
