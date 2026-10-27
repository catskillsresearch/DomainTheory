module

public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Continuous.mem_scottUnion
public import DomainTheory.DataTypesAsLattices.Continuous.scottUnion
public import DomainTheory.DataTypesAsLattices.Functionality.updateEnv_isScottContinuous_t
public import DomainTheory.DataTypesAsLattices.Lambda.minExtend
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.updateEnv

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def updateEnvUnion (t x idx : Pomega) : Pomega :=
  minExtend (fun n => updateEnv t x n) idx

namespace updateEnvUnion

theorem ofNat (t x : Pomega) (n : ℕ) :
    updateEnvUnion t x (DomainTheory.DataTypesAsLattices.ofNat n) = updateEnv t x n := by
  ext k
  constructor
  · intro hk
    obtain ⟨m, hm, hkm⟩ := Set.mem_iUnion₂.mp hk
    have : m = n := by
      simpa [DomainTheory.DataTypesAsLattices.ofNat, Set.singleton_subset_iff] using hm
    subst m
    exact hkm
  · intro hk
    exact Set.mem_iUnion₂.mpr ⟨n, by simp [DomainTheory.DataTypesAsLattices.ofNat], hk⟩

theorem isScottContinuous_idx (t x : Pomega) :
    IsScottContinuous (updateEnvUnion t x) :=
  minExtend.isScottContinuous (fun n => updateEnv t x n)

theorem isScottContinuous_t (x idx : Pomega) :
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
      IsScottContinuous.monotone (updateEnv_isScottContinuous_t x n) hm hkn⟩

end updateEnvUnion

end DomainTheory.DataTypesAsLattices
