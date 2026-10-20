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
public import DomainTheory.InformationSystems.Factoid83.mem_vPairRFinset
public import DomainTheory.InformationSystems.Factoid83.VEnt_pairR_inv

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

theorem VEnt_pairRFinset_of_EntSet {u v : Finset VToken}
    (hEnts : ∀ y ∈ u, VEnt v y) :
    .top ∈ v ∨ (∀ y ∈ vPairRFinset u, VEnt (vPairRFinset v) y) := by
  by_cases htop : .top ∈ v
  · exact Or.inl htop
  · refine Or.inr ?_
    intro y hy
    have hy' := hEnts _ (mem_vPairRFinset.1 hy)
    rcases VEnt_pairR_inv hy' with hm | hproj
    · exact False.elim (htop hm)
    · exact hproj

end InfoSys

end DomainTheory.InformationSystems
