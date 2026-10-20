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
import DomainTheory.ContinuousLattice.Constructions.proposition_2_8


namespace DomainTheory.ContinuousLattice

open Topology Set

variable {D : Type*} [CompleteLattice D]







/-- The Sierpiński space `Prop` (Scott's `𝕆`) is a continuous lattice: it is a finite complete
lattice, so Proposition 2.8 applies. -/
theorem isContinuousLattice_prop : IsContinuousLattice Prop :=
  proposition_2_8

end DomainTheory.ContinuousLattice
