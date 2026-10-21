/-ai
The packed combinator is combinatory.

Pairing preserves combinatory elements, applied to successor, predecessor, the conditional, K, and S.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.seq2_combinatory

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem Gpack_combinatory : IsCombinatory Gpack :=
  seq2_combinatory .suc
    (seq2_combinatory .pred
      (seq2_combinatory .cond (seq2_combinatory .K .S)))

end DomainTheory.DataTypesAsLattices
