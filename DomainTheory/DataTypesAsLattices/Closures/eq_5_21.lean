/-ai
Scott 1976, (5.21). Every set a is contained in V(a), the application of the closure combinator to a.

The application law rewrites the right-hand side as the graph of V(a). The inclusion of a in the graph of its own application, followed by the pointwise reverse inclusion of application of a in V(a), gives the containment.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_1
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_18_rev
public import DomainTheory.DataTypesAsLattices.Closures.Vcomb_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (5.21).** `a ⊆ V(a)`. -/
theorem eq_5_21 (a : Pomega) : a ⊆ funOf Vcomb a := by
  rw [Vcomb_app]
  exact (eq_5_1 a).trans (xi_star fun x => eq_5_18_rev a x)

end DomainTheory.DataTypesAsLattices
