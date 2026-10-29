module

public import DomainTheory.ContinuousLattice.Specialization.scottTopologicalSpace
import DomainTheory.ContinuousLattice.WayBelow.ScottOpen

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Topology Set

universe u

variable {X : Type*} {D : Type u} [TopologicalSpace X] [CompleteLattice D]

def SpecializationPreorder (x y : X) : Prop :=
  ∀ U, IsOpen U → x ∈ U → y ∈ U

namespace SpecializationPreorder

theorem iff_specializes {x y : X} :
    SpecializationPreorder x y ↔ y ⤳ x :=
  specializes_iff_forall_open.symm

variable {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]

variable {x : ι → D} {L y : D}

theorem scott_iff {x y : D} :
    @SpecializationPreorder D scottTopologicalSpace x y ↔ x ≤ y := by
  constructor
  · intro hxy
    by_contra h
    exact hxy {z | ¬ z ≤ y} (ScottOpen.isOpen_iff.mpr (ScottOpen.not_le y)) h (by simp)
  · intro hxy U hU hxU
    exact (ScottOpen.isOpen_iff.mp hU).1 hxy hxU

theorem map {Y : Type*} [TopologicalSpace Y] {x y : X}
    (hxy : SpecializationPreorder x y) {f : X → Y} (hf : Continuous f) :
    SpecializationPreorder (f x) (f y) := by
  intro U hU hxU
  exact hxy (f ⁻¹' U) (hU.preimage hf) hxU

end SpecializationPreorder

end DomainTheory.ContinuousLattice
