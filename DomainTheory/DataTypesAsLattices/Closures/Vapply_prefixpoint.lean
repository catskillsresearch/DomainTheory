/-ai
The universe value V(a)(x) is a prefixpoint of the step y ↦ x ∪ a(y): x is contained in it, and a of it is contained in it.

Equation (5.16) gives the first inclusion. For the second, any y that contains x and is closed under a also contains the universe value, because the universe value is the intersection of all such y. Monotonicity of application then carries a of the universe value into a(y), hence into y, and therefore into the intersection.
ai-/

module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_16

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- `V(a)(x)` is a prefixpoint of `y ↦ x ∪ a(y)`. -/
theorem Vapply_prefixpoint (a x : Pomega) :
    x ⊆ Vapply a x ∧ funOf a (Vapply a x) ⊆ Vapply a x := by
  refine ⟨eq_5_16 a x, ?_⟩
  intro k hk y hy
  have hV : Vapply a x ⊆ y := fun m hm => hm y hy
  exact hy.2 (funOf_monotone_right a hV hk)

end DomainTheory.DataTypesAsLattices
