module

public import Mathlib.Computability.Halting
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
