module

public import DomainTheory.DataTypesAsLattices.Pomega.e
public import Mathlib.Data.Set.Lattice.Indexed
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def minExtend (p : ℕ → Pomega) (x : Pomega) : Pomega :=
  ⋃ n ∈ x, p n

namespace minExtend

theorem bot (p : ℕ → Pomega) : minExtend p botElem = botElem := by
  simp [minExtend, botElem]

theorem isScottContinuous (p : ℕ → Pomega) :
    IsScottContinuous (minExtend p) := by
  constructor
  intro x
  ext k
  constructor
  · intro hk
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion₂.mp hk
    exact mem_scottUnion.mpr ⟨2 ^ n, by simp [e_pow2, Set.singleton_subset_iff, hn],
      by simp [minExtend, e_pow2, hkn]⟩
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion₂.mp hkm
    exact Set.mem_iUnion₂.mpr ⟨n, hm hn, hkn⟩

theorem union (p : ℕ → Pomega) (x y : Pomega) :
    minExtend p (x ∪ y) = minExtend p x ∪ minExtend p y := by
  ext k
  simp [minExtend, or_and_right, exists_or]

end minExtend

end DomainTheory.DataTypesAsLattices
