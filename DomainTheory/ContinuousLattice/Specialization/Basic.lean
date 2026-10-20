/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.ContinuousLattice.WayBelow
import Mathlib.Topology.Inseparable
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Order.ScottTopology
import Mathlib.Order.DirSupClosed

/-!
# Specialization order and Scott topology (Scott 1972, §2 opening)

Scott's §2 begins with the specialization order on a `T₀`-space and the induced (Scott)
topology on a complete lattice. Proposition 2.1 (monotone nets and least upper bounds) is
split into its two directions; the convergence-to-below direction is the mathematically
heavier half and is recorded as `proposition_2_1_of_le`.
-/

namespace DomainTheory.ContinuousLattice

open Topology Set

universe u

variable {X : Type*} {D : Type u} [TopologicalSpace X] [CompleteLattice D]

/-! ### Specialization order -/

/-- **Scott 1972, §2.** The *specialization order*: `x ⊑ y` when `x ∈ U` open implies `y ∈ U`. -/
def SpecializationLe (x y : X) : Prop :=
  ∀ U, IsOpen U → x ∈ U → y ∈ U

instance specializationPreorder : Preorder X where
  le := SpecializationLe
  le_refl x := fun _ _ hx => hx
  le_trans x y z hxy hyz U hU hxU := hyz U hU (hxy U hU hxU)

/-! ### Scott topology from `ScottOpen` -/

@[reducible] noncomputable def scottTopologicalSpace : TopologicalSpace D :=
  Topology.scott D univ

/-! ### Monotone nets and Proposition 2.1 -/

variable {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]

def IsMonotoneNet (x : ι → D) : Prop :=
  Monotone x

def ScottConvergesTo (x : ι → D) (y : D) : Prop :=
  ∀ U, ScottOpen U → y ∈ U → ∃ i, ∀ j ≥ i, x j ∈ U

variable {x : ι → D} {L y : D}
end DomainTheory.ContinuousLattice
