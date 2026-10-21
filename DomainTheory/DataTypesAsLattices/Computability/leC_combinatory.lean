/-ai
The comparison combinator is combinatory.

It is built by applying S and K to the zero test and the subtraction combinator.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.subC_combinatory
public import DomainTheory.DataTypesAsLattices.Computability.isZeroC_combinatory

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4















theorem leC_combinatory : IsCombinatory leC :=
  .app (.app .S (.app .K (.app .S (.app .K isZeroC_combinatory))))
    subC_combinatory

end DomainTheory.DataTypesAsLattices
