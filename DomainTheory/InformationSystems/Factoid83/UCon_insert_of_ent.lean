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
public import DomainTheory.InformationSystems.Factoid83.uForgetFinset_insert
public import DomainTheory.InformationSystems.Factoid83.UCon
public import DomainTheory.InformationSystems.Factoid83.UEnt
public import DomainTheory.InformationSystems.Factoid83.not_VEnt_insert_top_of_ent

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

theorem UCon_insert_of_ent {u : Finset UToken} {p : UToken}
    (h : UEnt u p) : UCon (insert p u) := by
  rcases h with ⟨hCon, hEnt⟩
  rw [UCon, uForgetFinset_insert]
  exact not_VEnt_insert_top_of_ent p.property hEnt hCon

end InfoSys

end DomainTheory.InformationSystems
