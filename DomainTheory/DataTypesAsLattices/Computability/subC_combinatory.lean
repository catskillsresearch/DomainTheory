/-ai
The subtraction combinator subC is combinatory.

It is obtained by applying S to K applied to the combinatory application combinator, and to S applied to K applied to the combinatory fixed-point combinator and to S applied to the closed interpretation of primRecStepTerm and to K applied to the combinatory step subStepC.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.subStepC_combinatory

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4












theorem subC_combinatory : IsCombinatory subC :=
  .app (.app .S (.app .K dollarC_combinatory))
    (.app (.app .S (.app .K Ycomb_combinatory))
      (.app (.app .S (theorem_2_4_closed primRecStepTerm))
        (.app .K subStepC_combinatory)))

end DomainTheory.DataTypesAsLattices
