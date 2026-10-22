module
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic


@[expose] public section

namespace DomainTheory.ContinuousLattice

open Topology Set

variable {D : Type*} [CompleteLattice D]

section InjectiveExtension

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {E : Type*} [CompleteLattice E]

/-- Scott's canonical extension of `f : X → E` along `e : X → Y` (Scott 1972, proof of 2.11):
`y ↦ ⊔ { ⊓ f''(e⁻¹V) : V an open neighbourhood of y }`. No topology on `E` is needed to *state*
the operator — it is purely order-theoretic. -/
def scottExtend (e : X → Y) (f : X → E) (y : Y) : E :=
  sSup {d | ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ d = sInf (f '' (e ⁻¹' V))}

end InjectiveExtension

end DomainTheory.ContinuousLattice
