/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

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
