module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.IsClosure
public import DomainTheory.DataTypesAsLattices.Closures.closureCompact
public import DomainTheory.DataTypesAsLattices.Closures.closure_expansive

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

theorem closureCompact_isCompact {a : Pomega} (ha : IsClosure a) (n : ℕ) :
    IsCompact (closureCompact a ha n) := by
  apply retractBasis_wayBelow ha.2
  exact ⟨n, closure_expansive ha (e n), rfl⟩

end DomainTheory.DataTypesAsLattices
