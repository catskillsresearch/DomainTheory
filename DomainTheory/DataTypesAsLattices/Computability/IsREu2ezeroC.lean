/-ai
The zero numeral is recursively enumerable.

It is the numeral of 0.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2enumeral

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


theorem IsRE.zeroC : IsRE zeroC :=
  IsRE.numeral 0

end DomainTheory.DataTypesAsLattices
