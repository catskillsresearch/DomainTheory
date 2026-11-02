module

public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.Language
import DomainTheory.DataTypesAsLattices.Continuous.mem_scottUnion

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

namespace succSet

theorem isScottContinuous : IsScottContinuous succSet := by
  constructor
  intro x
  ext k
  constructor
  · intro ⟨n, hn, hk⟩
    refine mem_scottUnion.mpr ⟨2 ^ n, by simp [e.pow2, Set.singleton_subset_iff, hn], ?_⟩
    exact ⟨n, by simp [e.pow2], hk⟩
  · intro hk
    obtain ⟨m, hm, n, hn, hk⟩ := mem_scottUnion.mp hk
    exact ⟨n, hm hn, hk⟩

theorem ofNat (j : ℕ) : succSet (ofNat j) = ofNat (j + 1) := by
  ext k
  simp [succSet]

end succSet

end DomainTheory.DataTypesAsLattices
