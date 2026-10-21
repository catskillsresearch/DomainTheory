/-ai
For a fixed element y, union on the left is Scott continuous.

Fix x and compare membership of an index n with membership in the Scott union. If n lies in x, the power 2 to the n is a witness: its enumeration is the singleton of n, contained in x, and n lies in the left summand of the union. If n lies in y, the zero enumeration is a witness, by the empty enumeration of 0, and n lies in the right summand. Conversely, a Scott-union witness contributes n from the left summand by containment of that finite enumeration in x, or from the right summand directly.
ai-/
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
