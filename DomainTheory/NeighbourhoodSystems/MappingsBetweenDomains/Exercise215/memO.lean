/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- Membership for `𝒪`: a neighbourhood is the master `Δ = univ` or the empty set. -/
def memO (X : Set (Fin 1)) : Prop := X = Set.univ ∨ X = ∅

end DomainTheory.NeighbourhoodSystems.Exercise215
