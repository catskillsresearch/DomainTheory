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
import DomainTheory.ContinuousLattice.Constructions.isContinuousLattice_prop


namespace DomainTheory.ContinuousLattice

open Topology Set

variable {D : Type*} [CompleteLattice D]







/-- A power of Scott's two-point space `𝕆 = Prop` is a continuous lattice: `Prop` is a continuous
lattice (`isContinuousLattice_prop`) and products of continuous lattices are continuous
(Proposition 2.9(a)). This is the order-theoretic content of "a Cartesian power of `𝕆` is a
continuous lattice", the construction Theorem 2.12 retracts onto. -/
theorem sierpinskiPower_isContinuousLattice (ι : Type*) : IsContinuousLattice (ι → Prop) :=
  proposition_2_9_a (fun _ => Prop) (fun _ => isContinuousLattice_prop)

end DomainTheory.ContinuousLattice
