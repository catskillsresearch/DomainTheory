/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Basic
public import DomainTheory.Neighborhood.Definition610.Basic
public import DomainTheory.Neighborhood.Definition610._root_u2eDomainTheoryu2eNeighborhoodu2eNeighborhoodSystemu2eext

@[expose] public section


namespace DomainTheory.Neighborhood

variable {α : Type*}



namespace Subsystem

/-- The subsystem relation is **antisymmetric**: `D ◁ E` and `E ◁ D` force `D = E`. (Mutual `sub`
gives equal `mem`, and `master_eq` gives equal masters.) -/
theorem antisymm {D E : NeighborhoodSystem α} (h₁ : D ◁ E) (h₂ : E ◁ D) : D = E :=
  NeighborhoodSystem.ext (fun _ => ⟨fun h => h₁.sub h, fun h => h₂.sub h⟩) h₁.master_eq

end Subsystem
end DomainTheory.Neighborhood
