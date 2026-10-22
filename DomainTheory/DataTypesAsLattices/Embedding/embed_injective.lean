/-ai
If the source is a T₀ space and the sets U n form a topological basis, the embedding along U is injective.

Equal images mean that the two points lie in exactly the same basis elements. They are then inseparable: any open neighbourhood of one contains a basis element around that point, and the other point lies in the same basis element, hence in the open. Inseparable points of a T₀ space are equal.
ai-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.FixedPoint
public import DomainTheory.DataTypesAsLattices.Embedding.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace Topology Function


theorem embed_injective {X : Type*} [TopologicalSpace X] [T0Space X]
    (U : ℕ → Set X) (hbasis : IsTopologicalBasis (Set.range U)) :
    Injective (embed U) := by
  intro x y hxy
  have hmem : ∀ n, x ∈ U n ↔ y ∈ U n := fun n =>
    show n ∈ embed U x ↔ n ∈ embed U y by rw [hxy]
  refine Inseparable.eq ?_
  refine inseparable_iff_forall_isOpen.mpr ?_
  intro V hV
  constructor
  · intro hx
    obtain ⟨t, ⟨n, rfl⟩, hxt, htV⟩ :=
      hbasis.mem_nhds_iff.mp (hV.mem_nhds hx)
    exact htV ((hmem n).mp hxt)
  · intro hy
    obtain ⟨t, ⟨n, rfl⟩, hyt, htV⟩ :=
      hbasis.mem_nhds_iff.mp (hV.mem_nhds hy)
    exact htV ((hmem n).mpr hyt)

end DomainTheory.DataTypesAsLattices
