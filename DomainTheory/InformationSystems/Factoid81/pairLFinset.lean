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

private def pairLInsert : TreeToken α → Finset (TreeToken α) → Finset (TreeToken α)
  | .pairL t => insert t
  | .bot | .atom _ | .pairR _ => id

private instance :
    LeftCommutative (pairLInsert : TreeToken α → Finset (TreeToken α) → Finset (TreeToken α)) :=
  ⟨fun p q s => by cases p <;> cases q <;> first | exact insert_comm' _ _ s | rfl⟩

def pairLFinset (u : Finset (TreeToken α)) : Finset (TreeToken α) :=
  Multiset.foldr pairLInsert (∅ : Finset (TreeToken α)) u.1

end InfoSys
end DomainTheory.InformationSystems
