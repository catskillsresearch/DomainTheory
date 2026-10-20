module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.applyNat
public import DomainTheory.DataTypesAsLattices.Enumeration.Ycode

@[expose] public section

set_option linter.unusedSectionVars false

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, Theorem 3.3 (iii).** `val(rec(n)) = val(n)(rec(n))`
via `Y` (the paper's `v`/`num` packaging is `recNat`). -/
noncomputable def recCode (n : ℕ) : ℕ := applyNat Ycode n

end DomainTheory.DataTypesAsLattices
