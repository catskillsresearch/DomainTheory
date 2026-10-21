/-ai
Scott 1976, (5.2). The identity combinator is contained in the function space of the identity combinator with itself.

The identity combinator is a closure, and the inclusion of the identity into a function space of closures applies to that closure on both sides.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.Icomb_isClosure
public import DomainTheory.DataTypesAsLattices.Closures.Icomb_subset_arrowR

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (5.2).** `I ⊆ I ∘→ I`. -/
theorem eq_5_2 : Icomb ⊆ arrowR Icomb Icomb :=
  Icomb_subset_arrowR Icomb_isClosure Icomb_isClosure

end DomainTheory.DataTypesAsLattices
