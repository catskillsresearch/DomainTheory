/-ai
Scott 1976, (5.17). The operation V(a) is idempotent on values.

If a set contains x and is closed under a, it contains V(a) applied to x, so it meets the witness condition for the double application. The opposite inclusion is the expansiveness of V(a) at its own value.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_16

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (5.17).** `V(a)` is idempotent. -/
theorem eq_5_17 (a x : Pomega) : Vapply a (Vapply a x) = Vapply a x := by
  apply subset_antisymm
  · intro k hk y hy
    have : Vapply a x ⊆ y := by
      intro m hm
      exact hm y hy
    exact hk y ⟨this, hy.2⟩
  · exact eq_5_16 a (Vapply a x)

end DomainTheory.DataTypesAsLattices
