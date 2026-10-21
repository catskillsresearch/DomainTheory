/-ai
For a fixed element u, the positive bar branch is Scott continuous in its second argument.

The substitution theorem composes right continuity of sequence cons at the numeral 1 with the composite, again by substitution, of right continuity of sequencing at u and left continuity of application at the numeral 1.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.seq2_right_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Enumeration.seqCons_right_isScottContinuous

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

















































theorem barPos_isScottContinuous_x (u : Pomega) :
    IsScottContinuous (fun x => barPos u x) :=
  theorem_1_3 (f := fun xs => seqCons (ofNat 1) xs)
    (g := fun x => seq2 u (funOf x (ofNat 1)))
    (seqCons_right_isScottContinuous (ofNat 1))
    (theorem_1_3 (seq2_right_isScottContinuous u)
      (funOf_isScottContinuous_left (ofNat 1)))

end DomainTheory.DataTypesAsLattices
