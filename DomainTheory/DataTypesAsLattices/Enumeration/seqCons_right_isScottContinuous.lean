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






































theorem seqCons_right_isScottContinuous (x : Pomega) :
    IsScottContinuous (fun xs => seqCons x xs) :=
  graph_const_isScottContinuous
    (fun xs z => condSet z x (funOf xs (predSet z)))
    (fun z => theorem_1_3 (condSet_isScottContinuous_right z x)
      (funOf_isScottContinuous_left (predSet z)))

end DomainTheory.DataTypesAsLattices
