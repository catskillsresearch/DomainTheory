module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.isOpen_memOpen
public import DomainTheory.DataTypesAsLattices.Continuous.memOpen
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Embedding.extend
public import DomainTheory.DataTypesAsLattices.Embedding.embed

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace Topology Function

theorem theorem_1_5 {Y : Type*} [TopologicalSpace Y] {X : Set Y}
    (f : X → Pomega) : Continuous (extend (Y := Y) (X := X) f) := by
  refine continuous_generateFrom_iff.2 ?_
  rintro _ ⟨k, rfl⟩
  exact extend.isOpen_mem f k

theorem theorem_1_5.extension {Y : Type*} [TopologicalSpace Y] {X : Set Y}
    (f : X → Pomega) (hf : Continuous f) (x : X) :
    extend (Y := Y) (X := X) f ↑x = f x := by
  apply subset_antisymm
  · intro k hk
    obtain ⟨U, _, hxU, hall⟩ := (extend.mem f).mp hk
    exact hall x hxU
  · intro k hk
    have hpre : IsOpen (f ⁻¹' memOpen k) :=
      IsOpen.preimage hf (isOpen_memOpen k)
    obtain ⟨U, hU, hrel⟩ := isOpen_induced_iff.mp hpre
    refine (extend.mem f).mpr ⟨U, hU, ?_, ?_⟩
    · have : x ∈ Subtype.val ⁻¹' U := by
        rwa [hrel]
      exact this
    · intro z hz
      have : z ∈ f ⁻¹' memOpen k := by
        rwa [← hrel]
      exact this

end DomainTheory.DataTypesAsLattices
