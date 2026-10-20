/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid36
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid44

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- Finite approximations of `x`: the set `{ū | u ∈ Con, u ⊆ x}`. -/
def finiteApproximants (x : sys.Element) : Set sys.Element :=
  {y | ∃ (u : Finset α) (hu : u ∈ sys.Con), ↑u ⊆ x.carrier ∧ y = sys.closure u hu}

end InfoSys

end DomainTheory.InformationSystems
