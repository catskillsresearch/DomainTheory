/-ai
For fixed x and index, the index-continuous environment update is Scott continuous in the environment t.

Fix t and compare membership of a number k. From the double union, some index n in the argument has k in the update of t at n. Continuity of that single update rewrites the membership as membership in its Scott union, which supplies an approximant m of t, and the same n and m place k in the Scott union of the updated unions. Conversely, membership in that Scott union supplies an approximant m and then an index n, and monotonicity of the continuous update at n carries the membership from m up to t.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.updateEnv_isScottContinuous_t

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem updateEnvUnion_isScottContinuous_t (x idx : Pomega) :
    IsScottContinuous (fun t => updateEnvUnion t x idx) := by
  constructor
  intro t
  ext k
  constructor
  · intro hk
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion₂.mp hk
    have : k ∈ scottUnion (fun t => updateEnv t x n) t := by
      rw [← (updateEnv_isScottContinuous_t x n).out t]; exact hkn
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp this
    exact mem_scottUnion.mpr ⟨m, hm, Set.mem_iUnion₂.mpr ⟨n, hn, hkm⟩⟩
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion₂.mp hkm
    exact Set.mem_iUnion₂.mpr ⟨n, hn,
      isScottContinuous_monotone (updateEnv_isScottContinuous_t x n) hm hkn⟩

end DomainTheory.DataTypesAsLattices
