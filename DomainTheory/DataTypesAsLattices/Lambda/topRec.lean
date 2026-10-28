module

public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.succSet
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def topRec (x : Pomega) : Pomega := ofNat 0 ∪ succSet x

namespace topRec

theorem isScottContinuous : IsScottContinuous topRec := by
  constructor
  intro x
  ext k
  constructor
  · intro hk
    rcases hk with hk | ⟨n, hn, rfl⟩
    · exact mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inl hk⟩
    · exact mem_scottUnion.mpr ⟨2 ^ n, by simp [e_pow2, Set.singleton_subset_iff, hn],
        Or.inr ⟨n, by simp [e_pow2], rfl⟩⟩
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    rcases hkm with hk | ⟨n, hn, rfl⟩
    · exact Or.inl hk
    · exact Or.inr ⟨n, hm hn, rfl⟩

end topRec

end DomainTheory.DataTypesAsLattices
