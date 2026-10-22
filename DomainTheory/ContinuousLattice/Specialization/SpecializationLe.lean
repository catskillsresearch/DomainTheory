module

public import Mathlib.Topology.Defs.Basic
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Topology Set

universe u

variable {X : Type*} {D : Type u} [TopologicalSpace X] [CompleteLattice D]

/-- **Scott 1972, §2.** The *specialization order*: `x ⊑ y` when `x ∈ U` open implies `y ∈ U`. -/
def SpecializationLe (x y : X) : Prop :=
  ∀ U, IsOpen U → x ∈ U → y ∈ U

end DomainTheory.ContinuousLattice
