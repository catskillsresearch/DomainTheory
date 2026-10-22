module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.FixedPoint

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace Topology Function

/-- **Scott 1976, Theorem 1.5.** Maximal continuous extension of
`f : X → Pω` along a subspace inclusion `X ⊆ Y`:
`f̄(y) = ⋃ { ⋂ {f(x) | x ∈ X ∩ U} | y ∈ U, U open in Y }`. -/
def extend {Y : Type*} [TopologicalSpace Y] {X : Set Y}
    (f : X → Pomega) (y : Y) : Pomega :=
  ⋃₀ { t | ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ t = ⋂₀ (f '' {x : X | ↑x ∈ U}) }

end DomainTheory.DataTypesAsLattices
