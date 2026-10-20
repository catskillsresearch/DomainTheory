/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- Upward-directed family of elements: any two have a common upper bound in the family. -/
def IsDirected (S : Set sys.Element) : Prop :=
  ∀ (x y : sys.Element), x ∈ S → y ∈ S → ∃ z ∈ S, x ≤ z ∧ y ≤ z

end InfoSys

end DomainTheory.InformationSystems
