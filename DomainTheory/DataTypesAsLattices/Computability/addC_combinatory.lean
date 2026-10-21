/-ai
The addition combinator is combinatory.

It is the application of S to K applied to the dollar combinator, and to S applied to K applied to Y, and to S applied to the closed interpretation of the primitive-recursion step term and to K applied to the successor step.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.addStepC_combinatory

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4









theorem addC_combinatory : IsCombinatory addC :=
  .app (.app .S (.app .K dollarC_combinatory))
    (.app (.app .S (.app .K Ycomb_combinatory))
      (.app (.app .S (theorem_2_4_closed primRecStepTerm))
        (.app .K addStepC_combinatory)))

end DomainTheory.DataTypesAsLattices
