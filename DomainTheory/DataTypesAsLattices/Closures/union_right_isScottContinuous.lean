/-ai
If a map is Scott continuous, then union on the left with a fixed set, after that map, is Scott continuous.

A member of the fixed set lies in the Scott union at the empty finite set. A member of the image lies in the Scott union of the map and remains in the right disjunct. Conversely, a left disjunct of a Scott-union witness already lies in the fixed set, and a right disjunct is lifted by monotonicity of the map.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem union_right_isScottContinuous (x : Pomega) {f : Pomega → Pomega}
    (hf : IsScottContinuous f) :
    IsScottContinuous (fun y => x ∪ f y) := by
  intro y
  ext k
  constructor
  · intro hk
    rcases hk with hk | hk
    · exact mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inl hk⟩
    · have : k ∈ scottUnion f y := by rwa [← hf y]
      obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp this
      exact mem_scottUnion.mpr ⟨n, hn, Or.inr hkn⟩
  · intro hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
    rcases hkn with hkn | hkn
    · exact Or.inl hkn
    · exact Or.inr (isScottContinuous_monotone hf hn hkn)

end DomainTheory.DataTypesAsLattices
