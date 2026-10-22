/-ai
Scott 1976, Theorem 1.5, the extension property: if f is continuous, the extension of f agrees with f at every point of the subspace.

If k lies in the extension at a subspace point x, the membership criterion supplies an open containing x on which every subspace value of f, including f(x), contains k. Conversely, if k lies in f(x), continuity makes the preimage of the subbasic open of k open in the subspace topology, so that preimage is the trace of an ambient open U. The trace relation puts x in U and puts k into f at every subspace point of U, so the membership criterion puts k in the extension.
ai-/
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


/-- **Scott 1976, Theorem 1.5**, extension property when `f` is continuous. -/
theorem theorem_1_5_extends {Y : Type*} [TopologicalSpace Y] {X : Set Y}
    (f : X → Pomega) (hf : Continuous f) (x : X) :
    extend (Y := Y) (X := X) f ↑x = f x := by
  apply subset_antisymm
  · intro k hk
    obtain ⟨U, _, hxU, hall⟩ := (mem_extend f).mp hk
    exact hall x hxU
  · intro k hk
    have hpre : IsOpen (f ⁻¹' memOpen k) :=
      IsOpen.preimage hf (isOpen_memOpen k)
    obtain ⟨U, hU, hrel⟩ := isOpen_induced_iff.mp hpre
    refine (mem_extend f).mpr ⟨U, hU, ?_, ?_⟩
    · have : x ∈ Subtype.val ⁻¹' U := by
        rwa [hrel]
      exact this
    · intro z hz
      have : z ∈ f ⁻¹' memOpen k := by
        rwa [← hrel]
      exact this

end DomainTheory.DataTypesAsLattices
