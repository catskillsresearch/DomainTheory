/-ai
Applying R to x returns the pair sequence of the numeral 0 with x.

This is the beta law for the graph of that map, using Scott continuity of pairing on the right with the numeral 0 held fixed.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.seq2_right_isScottContinuous

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code





































theorem Rcomb_app (x : Pomega) : funOf Rcomb x = seq2 (ofNat 0) x :=
  beta (seq2_right_isScottContinuous (ofNat 0)) x

end DomainTheory.DataTypesAsLattices
