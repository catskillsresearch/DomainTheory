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

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false
universe u
variable {α : Type*} [DecidableEq α]
variable (A : InfoSys α)

private def pairRInsert : TreeToken α → Finset (TreeToken α) → Finset (TreeToken α)
  | .pairR t => insert t
  | .bot | .atom _ | .pairL _ => id

private instance :
    LeftCommutative (pairRInsert : TreeToken α → Finset (TreeToken α) → Finset (TreeToken α)) :=
  ⟨fun p q s => by cases p <;> cases q <;> first | exact insert_comm' _ _ s | rfl⟩

def pairRFinset (u : Finset (TreeToken α)) : Finset (TreeToken α) :=
  Multiset.foldr pairRInsert (∅ : Finset (TreeToken α)) u.1

end InfoSys
end DomainTheory.InformationSystems
