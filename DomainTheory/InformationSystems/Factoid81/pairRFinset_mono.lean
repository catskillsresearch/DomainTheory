/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Product
public import DomainTheory.InformationSystems.Sum
public import DomainTheory.InformationSystems.Factoid81.TreeToken
public import DomainTheory.InformationSystems.Factoid81.TreeCon
public import DomainTheory.InformationSystems.Factoid81.TreeCon
public import DomainTheory.InformationSystems.Factoid81.atomFinset
public import DomainTheory.InformationSystems.Factoid81.pairLFinset
public import DomainTheory.InformationSystems.Factoid81.pairRFinset
public import DomainTheory.InformationSystems.Factoid81.mem_pairRFinset

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u

variable {α : Type*} [DecidableEq α]

theorem pairRFinset_mono {u v : Finset (TreeToken α)} (h : v ⊆ u) :
    pairRFinset v ⊆ pairRFinset u := fun _ ht => mem_pairRFinset.2 (h (mem_pairRFinset.1 ht))

end InfoSys

end DomainTheory.InformationSystems
