/-ai
If f is Scott continuous and A is a directed set of fixed points of f, then the union of the underlying values of A is itself a fixed point of f.

An element of the union lies in the Scott union of f along that union, by continuity. The finite piece witnessing membership in the Scott union is covered by some member of A, and monotonicity puts the element in the image of that member. The member is a fixed point, so the element lies in it and hence in the union. The opposite inclusion is the inequality of a union of fixed points against the image of that union.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.directed_finite_cover

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem directed_sUnion_fixed {f : Pomega → Pomega} (hf : IsScottContinuous f)
    {A : Set (Fixpoints f)} (hA : IsDirectedSet A) :
    ⋃₀ (Fixpoints.vals A) ∈ Fixpoints f := by
  apply subset_antisymm
  · intro k hk
    have hk' : k ∈ scottUnion f (⋃₀ (Fixpoints.vals A)) := by
      rwa [← hf (⋃₀ (Fixpoints.vals A))]
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk'
    obtain ⟨z, hzA, hnz⟩ :=
      directed_finite_cover hA (e_finite n) hn
    have : k ∈ f z :=
      isScottContinuous_monotone hf hnz hkn
    rw [z.property] at this
    exact Set.mem_sUnion.mpr ⟨z, ⟨z, hzA, rfl⟩, this⟩
  · exact sUnion_Fixpoints_le_image hf (Fixpoints.vals_subset A)

end DomainTheory.DataTypesAsLattices
