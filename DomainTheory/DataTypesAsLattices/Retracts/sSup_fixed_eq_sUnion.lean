module

public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.FixedLattices.DirectedSet
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.Fixpoints
public import DomainTheory.DataTypesAsLattices.Retracts.vals
public import DomainTheory.DataTypesAsLattices.Retracts.fixpointsCompleteLattice
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
