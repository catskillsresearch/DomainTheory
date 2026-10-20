/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120.upSet
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120.mem_upSet
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120.upSet_subset_iff

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- `X ↦ ↑X` is one-one on `𝒟`. -/
theorem upSet_injective {X Y : Set α} (hX : V.mem X) (hY : V.mem Y)
    (h : V.upSet X = V.upSet Y) : X = Y :=
  Set.Subset.antisymm ((V.upSet_subset_iff hX).mp h.subset)
    ((V.upSet_subset_iff hY).mp h.superset)

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
