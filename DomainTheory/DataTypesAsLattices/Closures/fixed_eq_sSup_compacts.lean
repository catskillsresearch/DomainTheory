/-ai
If a is a closure, the compact fixed points below a fixed point x form a directed set, and x is their supremum.

That set is the retract basis of x. The retract basis of a retract is directed, and its supremum is the fixed point.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.IsClosure
public import DomainTheory.DataTypesAsLattices.Closures.compactFixedBelow
public import DomainTheory.DataTypesAsLattices.Closures.retractBasis_eq_compactFixedBelow

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

theorem fixed_eq_sSup_compacts {a : Pomega} (ha : IsClosure a)
    (x : Fixpoints (funOf a)) :
    IsDirectedSet (compactFixedBelow a x) ∧
      x = sSup (compactFixedBelow a x) := by
  rw [← retractBasis_eq_compactFixedBelow ha x]
  exact ⟨retractBasis_directed ha.2 x, retractBasis_sSup ha.2 x⟩

end DomainTheory.DataTypesAsLattices
