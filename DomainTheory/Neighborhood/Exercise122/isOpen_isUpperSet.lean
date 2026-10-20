/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import Mathlib.Topology.Inseparable
import DomainTheory.Neighborhood.Exercise122.Basic


namespace DomainTheory.Neighborhood

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)







/-- **Exercise 1.22, condition (i).** Every open set is upward closed under the approximation order
`⊑`: if `x ∈ 𝒰` and `x ⊑ y` then `y ∈ 𝒰`. (This is a *consequence* of (ii): the basic
neighbourhood `[X] ⊆ 𝒰` witnessing `x ∈ 𝒰` also contains every `y ⊒ x`.) -/
theorem isOpen_isUpperSet {U : Set V.Element} (hU : IsOpen U) :
    ∀ ⦃x y : V.Element⦄, x ∈ U → x ≤ y → y ∈ U := by
  intro x y hxU hxy
  obtain ⟨X, hX, hXU⟩ := hU x hxU
  exact hXU (hxy X hX)

end NeighborhoodSystem
end DomainTheory.Neighborhood
