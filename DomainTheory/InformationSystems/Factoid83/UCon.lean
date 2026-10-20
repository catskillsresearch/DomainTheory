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

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

/-- Consistency for `U`: finite `u ⊆ D_U` with `u ⊬_V ∇` (Scott (9)). -/
def UCon (u : Finset UToken) : Prop :=
  ¬ VEnt (uForgetFinset u) .top

end InfoSys

end DomainTheory.InformationSystems
