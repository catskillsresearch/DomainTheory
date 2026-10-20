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
import DomainTheory.ContinuousLattice.Constructions.proposition_2_11


namespace DomainTheory.ContinuousLattice

open Topology Set

variable {D : Type*} [CompleteLattice D]







/-- **Scott 1972, Theorem 2.12 (forward direction).** Every continuous lattice is an injective
space under its Scott topology. This is the substantial half of the equivalence "injective
spaces = continuous lattices", and is exactly Proposition 2.11. -/
theorem theorem_2_12_forward {E : Type*} [CompleteLattice E] (hE : IsContinuousLattice E) :
    @IsInjectiveSpace E scottTopologicalSpace :=
  proposition_2_11 hE

end DomainTheory.ContinuousLattice
