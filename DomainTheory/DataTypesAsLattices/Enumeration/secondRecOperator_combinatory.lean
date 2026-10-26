
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.termDollarStep
public import DomainTheory.DataTypesAsLattices.Lambda.dollarC_combinatory
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
public import DomainTheory.DataTypesAsLattices.Enumeration.secondRecSubstC_combinatory
public import DomainTheory.DataTypesAsLattices.Enumeration.secondRecOperator

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem secondRecOperator_combinatory : IsCombinatory secondRecOperator :=
  .app (.app .S (.app .K dollarC.combinatory))
    (.app
      (.app .S (.app (.app .S (.app .K .S)) .K))
      (.app .K secondRecSubstC_combinatory))

end DomainTheory.DataTypesAsLattices
