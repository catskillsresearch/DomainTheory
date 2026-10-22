
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem sigmaJ_isScottContinuous (j : ℕ) : IsScottContinuous (sigmaJ j) := by
  constructor
  intro x
  ext p
  constructor
  · intro ⟨k, heq, hp⟩
    refine mem_scottUnion.mpr ⟨2 ^ pair j k, ?_, k, heq, ?_⟩
    · simpa [e_pow2, Set.singleton_subset_iff] using hp
    · simp [e_pow2]
  · intro hp
    obtain ⟨n, hn, k, heq, hpk⟩ := mem_scottUnion.mp hp
    exact ⟨k, heq, hn hpk⟩

end DomainTheory.DataTypesAsLattices
