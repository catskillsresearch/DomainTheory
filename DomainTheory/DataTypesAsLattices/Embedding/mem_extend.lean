module

public import Mathlib.Topology.Bases
import all Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
import all Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
import all Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
import all Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.FixedPoint
public import DomainTheory.DataTypesAsLattices.Embedding.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace Topology Function


theorem mem_extend {Y : Type*} [TopologicalSpace Y] {X : Set Y}
    (f : X → Pomega) {y : Y} {k : ℕ} :
    k ∈ extend (Y := Y) (X := X) f y ↔
      ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ ∀ x : X, ↑x ∈ U → k ∈ f x := by
  constructor
  · intro hk
    rcases Set.mem_sUnion.mp hk with ⟨t, ⟨U, hU, hy, rfl⟩, hkt⟩
    refine ⟨U, hU, hy, ?_⟩
    intro x hx
    exact Set.mem_sInter.mp hkt (f x) ⟨x, hx, rfl⟩
  · intro ⟨U, hU, hy, hall⟩
    refine Set.mem_sUnion.mpr ⟨⋂₀ (f '' {x : X | ↑x ∈ U}), ⟨U, hU, hy, rfl⟩, ?_⟩
    intro t ht
    rcases ht with ⟨x, hx, rfl⟩
    exact hall x hx

end DomainTheory.DataTypesAsLattices
