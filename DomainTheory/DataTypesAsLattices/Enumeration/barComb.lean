module

public import DomainTheory.DataTypesAsLattices.Enumeration.barStep
public import DomainTheory.DataTypesAsLattices.FixedPoint.fix
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Lambda.Ycomb
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Enumeration.barStepTerm
public import DomainTheory.DataTypesAsLattices.Lambda.Ycomb_more
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_5

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

def barComb : Pomega := fix barStep

namespace barComb

theorem combinatory : IsCombinatory barComb := by
  have hY : funOf Ycomb (interp barStepTerm (fun _ => botElem)) = barComb := by
    rw [barStepTerm.interp, theorem_2_5 barStep.isScottContinuous]
    rfl
  exact hY ▸ IsCombinatory.app Ycomb.combinatory (theorem_2_4.closed barStepTerm)

end barComb

end DomainTheory.DataTypesAsLattices
