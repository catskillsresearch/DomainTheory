
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.secondRecSubstC_combinatory
public import DomainTheory.DataTypesAsLattices.Enumeration.secondRecOperator

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem secondRecOperator_combinatory : IsCombinatory secondRecOperator :=
  .app (.app .S (.app .K dollarC_combinatory))
    (.app
      (.app .S (.app (.app .S (.app .K .S)) .K))
      (.app .K secondRecSubstC_combinatory))

end DomainTheory.DataTypesAsLattices
