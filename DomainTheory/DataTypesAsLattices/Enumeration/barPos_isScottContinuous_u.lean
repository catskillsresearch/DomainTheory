/-ai
For a fixed element x, the positive bar branch is Scott continuous in its first argument.

The substitution theorem composes right continuity of sequence cons at the numeral 1 with left continuity of sequencing at the application of x to the numeral 1.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.seq2_left_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Enumeration.seqCons_right_isScottContinuous

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem barPos_isScottContinuous_u (x : Pomega) :
    IsScottContinuous (fun u => barPos u x) :=
  theorem_1_3 (seqCons_right_isScottContinuous (ofNat 1))
    (seq2_left_isScottContinuous (funOf x (ofNat 1)))

end DomainTheory.DataTypesAsLattices
