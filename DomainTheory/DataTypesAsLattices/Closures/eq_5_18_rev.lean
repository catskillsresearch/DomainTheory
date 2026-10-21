/-ai
The reverse inclusion of (5.18): a applied to x is contained in V(a) applied to x. Whenever a set contains x and is closed under a, it contains a applied to x.

Right monotonicity of application of a sends the containment of x into a containment of a(x) in a(y), and closure of y under a puts that value inside y.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- The missing inclusion of (5.18): if `x ⊆ y` and `a(y) ⊆ y` then `a(x) ⊆ y`. -/
theorem eq_5_18_rev (a x : Pomega) :
    funOf a x ⊆ Vapply a x := by
  intro k hk y hy
  exact hy.2 (funOf_monotone_right a hy.1 hk)

end DomainTheory.DataTypesAsLattices
