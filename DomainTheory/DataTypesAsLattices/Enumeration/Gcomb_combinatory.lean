/-ai
The combinator G is combinatory.

Rewrite G as the application of the conditional to the packed combinators and then to zero, and close under application from the conditional, the packed combinators, and zero.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.Gpack_combinatory
public import DomainTheory.DataTypesAsLattices.Enumeration.Gcomb_eq_condC

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem Gcomb_combinatory : IsCombinatory Gcomb := by
  simpa [Gcomb_eq_condC] using
    IsCombinatory.app (IsCombinatory.app IsCombinatory.cond Gpack_combinatory)
      IsCombinatory.zero

end DomainTheory.DataTypesAsLattices
