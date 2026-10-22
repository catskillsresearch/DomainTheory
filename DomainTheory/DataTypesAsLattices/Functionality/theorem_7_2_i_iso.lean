/-ai
For a retract a, a(x) equals a(y) if and only if E_a relates a(x) and a(y). Classes of the kernel are represented by range elements.

If the two applications are equal, the retract law places both values in the range, so they are related. Conversely, relatedness includes equality of the two values.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- The spaces of `E_a` and of `{⟨x, y⟩ | a(x) = a(y)}` are isomorphic:
classes of the kernel are represented uniquely by range elements. -/
theorem theorem_7_2_i_iso {a : Pomega} (ha : Retract a) (x y : Pomega) :
    funOf a x = funOf a y ↔ (Ea a).rel (funOf a x) (funOf a y) := by
  constructor
  · intro h
    refine ⟨?_, ?_, h⟩
    · exact (retract_app ha x).symm
    · exact (retract_app ha y).symm
  · intro h
    exact h.2.2

end DomainTheory.DataTypesAsLattices
