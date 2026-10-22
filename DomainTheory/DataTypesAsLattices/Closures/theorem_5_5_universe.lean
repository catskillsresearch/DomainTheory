/-ai
Scott's theorem on the universe says that the universe combinator is itself a closure, and that its typed points are exactly the closure operations.

The universe combinator contains the identity combinator and is a retract. A set is a closure exactly when it equals the application of the universe combinator, and that equality is the typing equation read in either direction.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.theorem_5_5_iff
public import DomainTheory.DataTypesAsLattices.Closures.Vcomb_isRetract
public import DomainTheory.DataTypesAsLattices.Closures.Icomb_subset_Vcomb

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 5.5.** `V` itself is a closure, and its fixed
points are exactly the closure operations. -/
theorem theorem_5_5_universe :
    Closure Vcomb ∧ ∀ a, Closure a ↔ typed a Vcomb :=
  ⟨⟨⟨Icomb_subset_Vcomb, Vcomb_isRetract⟩⟩,
    fun a => (theorem_5_5_iff a).trans ⟨Eq.symm, Eq.symm⟩⟩

end DomainTheory.DataTypesAsLattices
