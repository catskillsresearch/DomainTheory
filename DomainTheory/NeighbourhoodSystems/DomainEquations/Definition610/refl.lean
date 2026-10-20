/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

variable {α : Type*}



namespace Subsystem

/-- The subsystem relation is **reflexive**: `D ◁ D`. (The `inter_closed` clause is trivial — the
hypothesis is already the conclusion.) -/
theorem refl (D : NeighborhoodSystem α) : D ◁ D where
  master_eq := rfl
  sub h := h
  inter_closed _ _ h := h

end Subsystem
end DomainTheory.NeighbourhoodSystems
