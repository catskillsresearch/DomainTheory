/-ai
The first projection of a disjoint pairing is Scott continuous.

If the double of a number lies in a set, the finite set whose only member is that double is contained in the set and contains the double, so the number lies in the first projection of that finite set and hence in the Scott union. Conversely, a Scott-union witness is a finite set contained in the original set whose first projection already contains the number, so the double lies in the original set.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem squareFst_isScottContinuous : IsScottContinuous squareFst := by
  intro x
  ext n
  constructor
  · intro hn
    refine mem_scottUnion.mpr ⟨2 ^ (2 * n), ?_, ?_⟩
    · simpa [e_pow2, Set.singleton_subset_iff, squareFst] using hn
    · simp [squareFst, e_pow2]
  · intro hn
    obtain ⟨m, hm, hnm⟩ := mem_scottUnion.mp hn
    exact hm hnm

end DomainTheory.DataTypesAsLattices
