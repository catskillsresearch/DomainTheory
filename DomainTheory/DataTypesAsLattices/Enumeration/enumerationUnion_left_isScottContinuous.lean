module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices































































theorem enumerationUnion_left_isScottContinuous (y : Pomega) :
    IsScottContinuous (fun x => x ∪ y) := by
  intro x
  ext n
  constructor
  · rintro (hn | hn)
    · exact mem_scottUnion.mpr ⟨2 ^ n,
        by simp [e_pow2, Set.singleton_subset_iff, hn],
        Or.inl (by simp [e_pow2])⟩
    · exact mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inr hn⟩
  · intro hn
    obtain ⟨i, hi, hni⟩ := mem_scottUnion.mp hn
    exact hni.elim (fun h => Or.inl (hi h)) Or.inr

end DomainTheory.DataTypesAsLattices
