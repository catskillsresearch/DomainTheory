module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.IsDomainApprox
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.BotApprox_any
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.flatMap
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.flatMap_refl
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.flatMap_rogue
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.flatMap_consistent
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.flatMap_idem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open InfoSys

open ApproximableMap

namespace Factoid84

theorem flatMap_isDomain : IsDomainApprox flatMap where
  refl := flatMap_refl
  idem := flatMap_idem
  bot := BotApprox_any flatMap
  rogue := flatMap_rogue
  consistent := flatMap_consistent

end Factoid84

end DomainTheory.InformationSystems
