/-ai
The multiplication combinator is combinatory.

It is assembled by applications of S, K, the dollar combinator, Y, the closed interpretation of the primitive-recursion step term, the numeral 0, and the addition combinator.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.addC_combinatory

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4













theorem mulC_combinatory : IsCombinatory mulC :=
  .app (.app .S (.app .K dollarC_combinatory))
    (.app (.app .S (.app .K Ycomb_combinatory))
      (.app (.app .S
          (.app .K (.app (theorem_2_4_closed primRecStepTerm)
            (ofNat_combinatory 0))))
        (.app (.app .S (.app .K .K)) addC_combinatory)))

end DomainTheory.DataTypesAsLattices
