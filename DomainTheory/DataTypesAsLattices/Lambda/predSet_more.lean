module

public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.Language
import DomainTheory.DataTypesAsLattices.Continuous.mem_scottUnion

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

namespace predSet

theorem isScottContinuous : IsScottContinuous predSet := by
  constructor
  intro x
  ext k
  constructor
  · intro hk
    refine mem_scottUnion.mpr ⟨2 ^ (k + 1), ?_, ?_⟩
    · simpa [e.pow2, Set.singleton_subset_iff, predSet] using hk
    · simp [predSet, e.pow2]
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    exact hm hkm

theorem ofNat_succ (j : ℕ) : predSet (ofNat (j + 1)) = ofNat j := by
  ext k
  simp [predSet, ofNat]

end predSet

end DomainTheory.DataTypesAsLattices
