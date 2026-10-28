module

public import DomainTheory.ContinuousLattice.WayBelow.ScottOpen
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Continuous
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Directed
public import Mathlib.Topology.Inseparable
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Order.ScottTopology
public import Mathlib.Order.DirSupClosed
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Topology Set

universe u

variable {X : Type*} {D : Type u} [TopologicalSpace X] [CompleteLattice D]

def SpecializationLe (x y : X) : Prop :=
  ∀ U, IsOpen U → x ∈ U → y ∈ U

namespace SpecializationLe

theorem iff_specializes {x y : X} :
    SpecializationLe x y ↔ y ⤳ x :=
  specializes_iff_forall_open.symm

variable {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]

variable {x : ι → D} {L y : D}

theorem scott_iff {x y : D} :
    @SpecializationLe D scottTopologicalSpace x y ↔ x ≤ y := by
  constructor
  · intro hxy
    by_contra h
    exact hxy {z | ¬ z ≤ y} (ScottOpen.isOpen_iff.mpr (ScottOpen.not_le y)) h (by simp)
  · intro hxy U hU hxU
    exact (ScottOpen.isOpen_iff.mp hU).1 hxy hxU

theorem map {Y : Type*} [TopologicalSpace Y] {x y : X}
    (hxy : SpecializationLe x y) {f : X → Y} (hf : Continuous f) :
    SpecializationLe (f x) (f y) := by
  intro U hU hxU
  exact hxy (f ⁻¹' U) (hU.preimage hf) hxU

end SpecializationLe

end DomainTheory.ContinuousLattice
