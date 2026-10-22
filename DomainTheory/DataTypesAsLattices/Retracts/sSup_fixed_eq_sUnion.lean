/-ai
In the fixed-point lattice of a Scott-continuous map, the underlying set of the supremum of a directed set of fixed points equals the union of their underlying sets.

The union of the underlying sets is itself a fixed point. The supremum lies below that fixed point because each member is contained in the union. An element of the union lies in some member, and that member lies below the supremum.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.directed_sUnion_fixed

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem sSup_fixed_eq_sUnion {f : Pomega → Pomega} (hf : IsScottContinuous f)
    {A : Set (Fixpoints f)} (hA : DirectedSet A) :
    ((@sSup (Fixpoints f) (fixpointsCompleteLattice hf).toSupSet A :
        Fixpoints f) : Pomega) =
      ⋃₀ (Fixpoints.vals A) := by
  let := fixpointsCompleteLattice hf
  let u : Fixpoints f :=
    ⟨⋃₀ (Fixpoints.vals A), directed_sUnion_fixed hf hA⟩
  apply subset_antisymm
  · have hle : sSup A ≤ u := by
      apply sSup_le
      intro x hx
      exact Set.subset_sUnion_of_mem ⟨x, hx, rfl⟩
    exact hle
  · intro k hk
    obtain ⟨x, hxA, hkx⟩ := Set.mem_sUnion.mp hk
    obtain ⟨y, hyA, rfl⟩ := hxA
    exact (le_sSup hyA) hkx

end DomainTheory.DataTypesAsLattices
