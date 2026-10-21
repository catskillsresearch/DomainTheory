/-ai
Applying the composition of u and v to x yields the application of u to the application of v to x.

This is beta reduction. Continuity of the abstracted map is the substitution theorem applied to continuity of application of u and continuity of application of v.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


















































theorem enumComp_app (u v x : Pomega) :
    funOf (enumComp u v) x = funOf u (funOf v x) :=
  beta (theorem_1_3 (funOf_isScottContinuous u) (funOf_isScottContinuous v)) x

end DomainTheory.DataTypesAsLattices
