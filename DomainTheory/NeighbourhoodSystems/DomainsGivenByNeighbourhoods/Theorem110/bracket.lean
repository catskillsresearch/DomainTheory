/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- Scott's `[X] = {x ∈ |𝒟| ∣ X ∈ x}`: the elements of `|𝒟|` that contain the neighbourhood `X`.
(This is the `basicOpen X` of Exercise 1.22, repeated here to avoid the topology dependency.) -/
def bracket (X : Set α) : Set V.Element := {x | x.mem X}

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
