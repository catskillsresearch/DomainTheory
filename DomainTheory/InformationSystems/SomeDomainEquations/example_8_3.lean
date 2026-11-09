module

public import DomainTheory.InformationSystems.SomeDomainEquations.uSystem

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

open uSystem

set_option linter.unusedVariables false

theorem example_8_3 : UCon (∅ : Finset UToken) :=
  UCon_empty

end DomainTheory.InformationSystems.InfoSys
