/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.ContinuousLattice.MilnerCorrection
import DomainTheory.ContinuousLattice.ScottMaps
import DomainTheory.ContinuousLattice.Injective
import Mathlib.Order.Preorder.Finite
import DomainTheory.ContinuousLattice.Constructions.Basic
import DomainTheory.ContinuousLattice.Constructions.proposition_2_9_a
import DomainTheory.ContinuousLattice.Constructions.proposition_2_9_b


namespace DomainTheory.ContinuousLattice

open Topology Set

variable {D : Type*} [CompleteLattice D]





/-- **Scott 1972, Proposition 2.9 (full statement).** The product of a family of continuous lattices
is again a continuous lattice (`proposition_2_9_a`) whose Scott topology agrees with the product
topology (`proposition_2_9_b`). -/
theorem proposition_2_9 {ι : Type*} (E : ι → Type*) [∀ i, CompleteLattice (E i)]
    (hE : ∀ i, IsContinuousLattice (E i)) :
    IsContinuousLattice (∀ i, E i) ∧
      (scottTopologicalSpace : TopologicalSpace (∀ i, E i)) =
        @Pi.topologicalSpace ι E (fun _ => scottTopologicalSpace) :=
  ⟨proposition_2_9_a E hE, proposition_2_9_b E hE⟩

end DomainTheory.ContinuousLattice
