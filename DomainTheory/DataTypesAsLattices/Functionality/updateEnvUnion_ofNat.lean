module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






































theorem updateEnvUnion_ofNat (t x : Pomega) (n : ℕ) :
    updateEnvUnion t x (ofNat n) = updateEnv t x n := by
  ext k
  constructor
  · intro hk
    obtain ⟨m, hm, hkm⟩ := Set.mem_iUnion₂.mp hk
    have : m = n := by
      simpa [ofNat, Set.singleton_subset_iff] using hm
    subst m
    exact hkm
  · intro hk
    exact Set.mem_iUnion₂.mpr ⟨n, by simp [ofNat], hk⟩

end DomainTheory.DataTypesAsLattices
