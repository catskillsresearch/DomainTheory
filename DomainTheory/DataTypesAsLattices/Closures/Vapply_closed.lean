/-ai
The universe value V(a)(x) contains both x and a of that value. Scott's Theorem 5.6 and equation (5.15) record this closedness.

Equation (5.16) puts x inside the universe value. The universe value is a prefixpoint of the step y ↦ x ∪ a(y), so a of the universe value is contained in it as well. Their union is therefore contained in the universe value.
ai-/

module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_16
public import DomainTheory.DataTypesAsLattices.Closures.Vapply_prefixpoint

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 5.6 / (5.15).** The universe applied to `x` is
closed under `a` and contains `x`. -/
theorem Vapply_closed (a x : Pomega) :
    x ∪ funOf a (Vapply a x) ⊆ Vapply a x := by
  intro k hk
  rcases hk with hk | hk
  · exact eq_5_16 a x hk
  · exact (Vapply_prefixpoint a x).2 hk

end DomainTheory.DataTypesAsLattices
