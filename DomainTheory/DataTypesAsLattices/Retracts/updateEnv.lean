module

public import DomainTheory.DataTypesAsLattices.Lambda.Language
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.Lambda.const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more
public import DomainTheory.DataTypesAsLattices.Continuous.mem_scottUnion
public import DomainTheory.DataTypesAsLattices.Continuous.scottUnion
public import DomainTheory.DataTypesAsLattices.Lambda.Extend

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def updateEnv (t x : Pomega) (n : ℕ) : Pomega :=
  graph (fun m => if m = ofNat n then x else funOf t m)

namespace updateEnv

theorem isScottContinuous_t (x : Pomega) (n : ℕ) :
    IsScottContinuous (fun t => updateEnv t x n) :=
  graph_const_isScottContinuous
    (fun t m => if m = ofNat n then x else funOf t m)
    (fun m => by
      by_cases h : m = ofNat n
      · simpa [h] using const_isScottContinuous (c := x)
      · simpa [h] using funOf.isScottContinuous_left m)

def union (t x idx : Pomega) : Pomega :=
  minExtend (fun n => updateEnv t x n) idx

theorem ofNat (t x : Pomega) (n : ℕ) :
    union t x (DomainTheory.DataTypesAsLattices.ofNat n) = updateEnv t x n := by
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
    IsScottContinuous (union t x) :=
  minExtend.isScottContinuous (fun n => updateEnv t x n)

theorem union_isScottContinuous_t (x idx : Pomega) :
    IsScottContinuous (fun t => union t x idx) := by
  constructor
  intro t
  ext k
  constructor
  · intro hk
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion₂.mp hk
    have : k ∈ scottUnion (fun t => updateEnv t x n) t := by
      rw [← (updateEnv.isScottContinuous_t x n).out t]; exact hkn
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp this
    exact mem_scottUnion.mpr ⟨m, hm, Set.mem_iUnion₂.mpr ⟨n, hn, hkm⟩⟩
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion₂.mp hkm
    exact Set.mem_iUnion₂.mpr ⟨n, hn,
      IsScottContinuous.monotone (updateEnv.isScottContinuous_t x n) hm hkn⟩

end updateEnv

end DomainTheory.DataTypesAsLattices
