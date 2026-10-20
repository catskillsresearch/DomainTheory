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


namespace DomainTheory.ContinuousLattice

open Topology Set

variable {D : Type*} [CompleteLattice D]







/-- **Scott 1972, Theorem 2.12 (backward, Sierpiński base case).** `Prop` is a continuous
lattice (`isContinuousLattice_prop`), so its injectivity (Proposition 1.2) is an instance of the
equivalence. -/
theorem theorem_2_12_sierpinski_backward (_h : IsContinuousLattice Prop) : IsInjectiveSpace Prop :=
  proposition_1_2

end DomainTheory.ContinuousLattice
