module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.interStep
public import DomainTheory.DataTypesAsLattices.Lambda.interC
public import DomainTheory.DataTypesAsLattices.Lambda.termDollarStep
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_4
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_5
public import DomainTheory.DataTypesAsLattices.Lambda.interStep_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.Ycomb_combinatory
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_4_more
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Functionality.sumMed
public import DomainTheory.DataTypesAsLattices.Functionality.Zcomb
public import DomainTheory.DataTypesAsLattices.Functionality.sigmaJ
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.Icomb
public import DomainTheory.DataTypesAsLattices.Retracts.intF
public import DomainTheory.DataTypesAsLattices.Retracts.intR
public import DomainTheory.DataTypesAsLattices.Retracts.boolR
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.interStepTerm
public import DomainTheory.DataTypesAsLattices.Enumeration.interStepTerm_interp

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem interC_combinatory : IsCombinatory interC := by
  have hbody : IsCombinatory (graph interStep) := by
    rw [← interStepTerm_interp]
    exact theorem_2_4.closed interStepTerm
  have hfix := IsCombinatory.app Ycomb_combinatory hbody
  rw [theorem_2_5 interStep_isScottContinuous] at hfix
  exact hfix

end DomainTheory.DataTypesAsLattices
