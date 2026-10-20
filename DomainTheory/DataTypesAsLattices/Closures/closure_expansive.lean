module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.IsClosure

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

theorem closure_expansive {a : Pomega} (ha : IsClosure a) (x : Pomega) :
    x ⊆ funOf a x := by
  have := funOf_monotone_left ha.1 x
  rwa [Icomb_app] at this

end DomainTheory.DataTypesAsLattices
