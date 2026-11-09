module

public import DomainTheory.InformationSystems.SomeDomainEquations.DomainApprox

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

open DomainApprox
open InfoSys ApproximableMap

theorem example_8_4 : ¬ RogueApprox (idMap P) :=
  not_RogueApprox_idMap

end DomainTheory.InformationSystems.InfoSys
