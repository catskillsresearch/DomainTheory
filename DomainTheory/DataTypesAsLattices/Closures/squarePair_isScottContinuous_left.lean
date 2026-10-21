/-ai
Disjoint pairing is Scott continuous in the first argument, for a fixed second argument.

An even member, the double of an element of the varying set, lies in the Scott union at the finite set whose only member is that element. An odd member, coming from the fixed second set, lies in the Scott union at the empty finite set. Conversely, an even Scott-union witness pulls its first component back along the finite inclusion, and an odd witness is unchanged.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices































theorem squarePair_isScottContinuous_left (y : Pomega) :
    IsScottContinuous (fun x => squarePair x y) := by
  intro x
  ext k
  constructor
  · intro hk
    rcases hk with ⟨n, hn, hk⟩ | ⟨m, hm, hk⟩
    · exact mem_scottUnion.mpr ⟨2 ^ n, by simp [e_pow2, Set.singleton_subset_iff, hn],
        Or.inl ⟨n, by simp [e_pow2], hk⟩⟩
    · exact mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inr ⟨m, hm, hk⟩⟩
  · intro hk
    obtain ⟨p, hp, hkp⟩ := mem_scottUnion.mp hk
    rcases hkp with ⟨n, hn, hk⟩ | ⟨m, hm, hk⟩
    · exact Or.inl ⟨n, hp hn, hk⟩
    · exact Or.inr ⟨m, hm, hk⟩

end DomainTheory.DataTypesAsLattices
