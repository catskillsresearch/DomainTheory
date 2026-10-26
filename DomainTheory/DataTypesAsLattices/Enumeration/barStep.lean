module

public import DomainTheory.DataTypesAsLattices.Enumeration.barStepBody

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

def barStep (B : Pomega) : Pomega :=
  graph (fun u => graph (fun x => barStepBody B u x))

end DomainTheory.DataTypesAsLattices
