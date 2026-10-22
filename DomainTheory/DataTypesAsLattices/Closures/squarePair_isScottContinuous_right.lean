module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem squarePair_isScottContinuous_right (x : Pomega) :
    IsScottContinuous (fun y => squarePair x y) := by
  constructor
  intro y
  ext k
  constructor
  · intro hk
    rcases hk with ⟨n, hn, hk⟩ | ⟨m, hm, hk⟩
    · exact mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inl ⟨n, hn, hk⟩⟩
    · exact mem_scottUnion.mpr ⟨2 ^ m, by simp [e_pow2, Set.singleton_subset_iff, hm],
        Or.inr ⟨m, by simp [e_pow2], hk⟩⟩
  · intro hk
    obtain ⟨p, hp, hkp⟩ := mem_scottUnion.mp hk
    rcases hkp with ⟨n, hn, hk⟩ | ⟨m, hm, hk⟩
    · exact Or.inl ⟨n, hn, hk⟩
    · exact Or.inr ⟨m, hp hm, hk⟩

end DomainTheory.DataTypesAsLattices
