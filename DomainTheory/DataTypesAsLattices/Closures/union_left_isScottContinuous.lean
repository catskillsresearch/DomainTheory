/-ai
Union on the right with a fixed set is Scott continuous.

A member of the varying set lies in the Scott union of the identity, hence in some finite piece contained in the set, and remains in the left disjunct of the union. A member of the fixed set lies in the Scott union at the empty finite set. Conversely, a left disjunct of a Scott-union witness is lifted by monotonicity of the identity, and a right disjunct already lies in the fixed set.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem union_left_isScottContinuous (c : Pomega) :
    IsScottContinuous (fun x => x ∪ c) := by
  intro x
  ext k
  constructor
  · intro hk
    rcases hk with hk | hk
    · have : k ∈ scottUnion (fun z => z) x := by
        rw [← id_isScottContinuous x]; exact hk
      obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp this
      exact mem_scottUnion.mpr ⟨n, hn, Or.inl hkn⟩
    · exact mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inr hk⟩
  · intro hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
    rcases hkn with hkn | hkn
    · exact Or.inl (isScottContinuous_monotone id_isScottContinuous hn hkn)
    · exact Or.inr hkn

end DomainTheory.DataTypesAsLattices
