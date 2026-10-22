module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


theorem enumerationUnion_right_isScottContinuous (x : Pomega) :
    IsScottContinuous (fun y => x ∪ y) := by
  constructor
  intro y
  ext n
  constructor
  · rintro (hn | hn)
    · exact mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inl hn⟩
    · exact mem_scottUnion.mpr ⟨2 ^ n,
        by simp [e_pow2, Set.singleton_subset_iff, hn],
        Or.inr (by simp [e_pow2])⟩
  · intro hn
    obtain ⟨i, hi, hni⟩ := mem_scottUnion.mp hn
    exact hni.elim Or.inl (fun h => Or.inr (hi h))

end DomainTheory.DataTypesAsLattices
