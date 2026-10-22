module

public import Mathlib.Computability.Halting
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
