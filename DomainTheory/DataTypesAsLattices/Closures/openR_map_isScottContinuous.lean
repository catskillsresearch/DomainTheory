module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem openR_map_isScottContinuous :
    IsScottContinuous (fun u => {m | ∃ n, e n ⊆ e m ∧ n ∈ u}) := by
  constructor
  intro u
  ext m
  constructor
  · intro ⟨n, hn, hnu⟩
    exact mem_scottUnion.mpr ⟨2 ^ n, by simp [e_pow2, Set.singleton_subset_iff, hnu],
      ⟨n, hn, by simp [e_pow2]⟩⟩
  · intro hm
    obtain ⟨k, hk, n, hn, hnk⟩ := mem_scottUnion.mp hm
    exact ⟨n, hn, hk hnk⟩

end DomainTheory.DataTypesAsLattices
