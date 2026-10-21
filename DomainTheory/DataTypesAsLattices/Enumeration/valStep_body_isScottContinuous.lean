/-ai
For each v, the body of the enumerator step is Scott continuous. That body sends a code k to the McCarthy conditional of k, with zero branch the G combinator and positive branch the minimal extension of the application selected by v at k.

The binary substitution form of Theorem 1.3 combines continuity of the conditional in its test and in its positive branch with continuity of the identity and continuity of minimal extension at the applications selected by v.
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



























theorem valStep_body_isScottContinuous (v : Pomega) :
    IsScottContinuous (fun k =>
      condSet k Gcomb (minExtend (valStepValue v) k)) :=
  theorem_1_3_tuple
    (fun y => condSet_isScottContinuous_left Gcomb y)
    (fun z => condSet_isScottContinuous_right z Gcomb)
    id_isScottContinuous
    (minExtend_isScottContinuous (valStepValue v))

end DomainTheory.DataTypesAsLattices
