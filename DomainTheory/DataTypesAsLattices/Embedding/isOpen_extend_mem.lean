module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.FixedPoint
public import DomainTheory.DataTypesAsLattices.Embedding.Basic
public import DomainTheory.DataTypesAsLattices.Embedding.mem_extend

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace Topology Function


theorem isOpen_extend_mem {Y : Type*} [TopologicalSpace Y] {X : Set Y}
    (f : X → Pomega) (k : ℕ) :
    IsOpen {y : Y | k ∈ extend (Y := Y) (X := X) f y} := by
  have : {y : Y | k ∈ extend (Y := Y) (X := X) f y} =
      ⋃ U ∈ {U : Set Y | IsOpen U ∧ ∀ x : X, ↑x ∈ U → k ∈ f x}, U := by
    ext y
    constructor
    · intro hy
      obtain ⟨U, hU, hyU, hall⟩ := (mem_extend f).mp hy
      exact Set.mem_iUnion₂.mpr ⟨U, ⟨hU, hall⟩, hyU⟩
    · intro hy
      obtain ⟨U, hU, hyU⟩ := Set.mem_iUnion₂.mp hy
      exact (mem_extend f).mpr ⟨U, hU.1, hyU, hU.2⟩
  rw [this]
  exact isOpen_biUnion fun _ hU => hU.1

end DomainTheory.DataTypesAsLattices
