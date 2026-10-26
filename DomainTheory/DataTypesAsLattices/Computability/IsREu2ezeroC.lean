module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda.zeroC
public import DomainTheory.DataTypesAsLattices.Computability.IsRE
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2enumeral

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


theorem IsRE.zeroC : IsRE zeroC :=
  IsRE.numeral 0

end DomainTheory.DataTypesAsLattices
