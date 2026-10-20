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
public import DomainTheory.InformationSystems.Factoid84.mem_barElement
public import DomainTheory.InformationSystems.Factoid84.flatMap
public import DomainTheory.InformationSystems.Factoid84.flatMap_toElement_of_mem_one

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open InfoSys

open ApproximableMap

namespace Factoid84

theorem flatMap_rogue : RogueApprox flatMap :=
  flatMap_toElement_of_mem_one ((mem_barElement 1 1).2 (Or.inr rfl))

end Factoid84

end DomainTheory.InformationSystems
