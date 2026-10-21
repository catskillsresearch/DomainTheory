/-ai
The recursion code of a natural number n is the application of the Y-code to n. In Scott's Theorem 3.3 (iii) the value of this code satisfies val(rec(n)) = val(n)(rec(n)) through the fixed-point combinator Y; the paper's packaging of v and num is the companion function recNat.
ai-/

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

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, Theorem 3.3 (iii).** `val(rec(n)) = val(n)(rec(n))`
via `Y` (the paper's `v`/`num` packaging is `recNat`). -/
noncomputable def recCode (n : ℕ) : ℕ := applyNat Ycode n

end DomainTheory.DataTypesAsLattices
