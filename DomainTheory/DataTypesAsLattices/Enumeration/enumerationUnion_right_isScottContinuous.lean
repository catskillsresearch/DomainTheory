/-ai
For a fixed element x, union on the right is Scott continuous.

Fix y and compare membership of an index n with membership in the Scott union. If n lies in x, the zero enumeration is a witness and n lies in the left summand. If n lies in y, the power 2 to the n is a witness: its enumeration is the singleton of n, contained in y, and n lies in the right summand. Conversely, a Scott-union witness contributes n from the left summand directly, or from the right summand by containment of that finite enumeration in y.
ai-/
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
