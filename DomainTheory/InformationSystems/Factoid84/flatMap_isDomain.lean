/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Proposition55
public import DomainTheory.InformationSystems.Factoid34
public import DomainTheory.InformationSystems.Factoid35
public import DomainTheory.InformationSystems.Factoid84.IsDomainApprox
public import DomainTheory.InformationSystems.Factoid84.BotApprox_any
public import DomainTheory.InformationSystems.Factoid84.flatMap
public import DomainTheory.InformationSystems.Factoid84.flatMap_refl
public import DomainTheory.InformationSystems.Factoid84.flatMap_rogue
public import DomainTheory.InformationSystems.Factoid84.flatMap_consistent
public import DomainTheory.InformationSystems.Factoid84.flatMap_idem

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
