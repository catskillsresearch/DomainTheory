/-ai
The second projection of a disjoint pairing is Scott continuous.

If the double plus one of a number lies in a set, the finite set whose only member is that double plus one is contained in the set and contains that element, so the number lies in the second projection of the finite set and hence in the Scott union. Conversely, a Scott-union witness is a finite set contained in the original set whose second projection already contains the number, so the double plus one lies in the original set.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem squareSnd_isScottContinuous : IsScottContinuous squareSnd := by
  intro x
  ext m
  constructor
  · intro hm
    refine mem_scottUnion.mpr ⟨2 ^ (2 * m + 1), ?_, ?_⟩
    · simpa [e_pow2, Set.singleton_subset_iff, squareSnd] using hm
    · simp [squareSnd, e_pow2]
  · intro hm
    obtain ⟨k, hk, hkm⟩ := mem_scottUnion.mp hm
    exact hk hkm

end DomainTheory.DataTypesAsLattices
