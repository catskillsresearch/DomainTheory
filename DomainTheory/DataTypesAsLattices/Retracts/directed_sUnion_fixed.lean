module

public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.FixedLattices.DirectedSet
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.mem_scottUnion
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Continuous.scottUnion
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.Fixpoints
public import DomainTheory.DataTypesAsLattices.Retracts.vals
public import DomainTheory.DataTypesAsLattices.Retracts.sUnion_Fixpoints_le_image
public import DomainTheory.DataTypesAsLattices.Retracts.directed_finite_cover

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem directed_sUnion_fixed {f : Pomega → Pomega} (hf : IsScottContinuous f)
    {A : Set (Fixpoints f)} (hA : DirectedSet A) :
    ⋃₀ (Fixpoints.vals A) ∈ Fixpoints f := by
  apply subset_antisymm
  · intro k hk
    have hk' : k ∈ scottUnion f (⋃₀ (Fixpoints.vals A)) := by
      rwa [← hf.out (⋃₀ (Fixpoints.vals A))]
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk'
    obtain ⟨z, hzA, hnz⟩ :=
      directed_finite_cover hA (e_finite n) hn
    have : k ∈ f z :=
      IsScottContinuous.monotone hf hnz hkn
    rw [z.property] at this
    exact Set.mem_sUnion.mpr ⟨z, ⟨z, hzA, rfl⟩, this⟩
  · exact sUnion_Fixpoints_le_image hf (Fixpoints.vals.subset A)

end DomainTheory.DataTypesAsLattices
