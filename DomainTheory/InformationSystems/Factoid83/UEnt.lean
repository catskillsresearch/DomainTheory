/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Product
public import DomainTheory.InformationSystems.Factoid83.VToken
public import DomainTheory.InformationSystems.Factoid83.VEnt
public import DomainTheory.InformationSystems.Factoid83.VEnt
public import DomainTheory.InformationSystems.Factoid83.vPairLFinset
public import DomainTheory.InformationSystems.Factoid83.vPairRFinset
public import DomainTheory.InformationSystems.Factoid83.BasicInst33
public import DomainTheory.InformationSystems.Factoid83.UToken
public import DomainTheory.InformationSystems.Factoid83.BasicInst35
public import DomainTheory.InformationSystems.Factoid83.BasicInst39
public import DomainTheory.InformationSystems.Factoid83.uForgetFinset
public import DomainTheory.InformationSystems.Factoid83.UCon

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

/-- Entailment for `U` (Scott (10)). -/
def UEnt (u : Finset UToken) (p : UToken) : Prop :=
  UCon u ∧ VEnt (uForgetFinset u) p.val

end InfoSys

end DomainTheory.InformationSystems
