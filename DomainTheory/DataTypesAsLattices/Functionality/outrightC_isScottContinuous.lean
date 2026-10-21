/-ai
The map sending u to the conditional set of its first component, with bottom as the zero branch and its second component as the positive branch, is Scott continuous.

The binary continuity theorem applies to continuity of the conditional set in its test and in its positive branch, together with continuity of application in the function argument at zero and at one.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_tuple

@[expose] public section


namespace DomainTheory.DataTypesAsLattices





















theorem outrightC_isScottContinuous :
    IsScottContinuous (fun u =>
      condSet (funOf u (ofNat 0)) botElem (funOf u (ofNat 1))) :=
  continuous_tuple
    (fun y => condSet_isScottContinuous_left botElem y)
    (fun tes => condSet_isScottContinuous_right tes botElem)
    (funOf_isScottContinuous_left (ofNat 0))
    (funOf_isScottContinuous_left (ofNat 1))

end DomainTheory.DataTypesAsLattices
