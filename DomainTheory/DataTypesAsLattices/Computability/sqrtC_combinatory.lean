/-ai
The integer-square-root combinator sqrtC is combinatory.

It is built by applying S to the application of S to K applied to the combinatory element primRecZeroC and to the combinatory element sqrtStepC, and to the application of S to K and to K.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.primRecZeroC_combinatory
public import DomainTheory.DataTypesAsLattices.Computability.sqrtStepC_combinatory

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4

























theorem sqrtC_combinatory : IsCombinatory sqrtC :=
  .app
    (.app .S
      (.app (.app .S (.app .K primRecZeroC_combinatory))
        sqrtStepC_combinatory))
    (.app (.app .S .K) .K)

end DomainTheory.DataTypesAsLattices
