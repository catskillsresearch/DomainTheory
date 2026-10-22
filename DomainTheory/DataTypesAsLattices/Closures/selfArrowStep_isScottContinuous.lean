/-ai
The self-arrow step is Scott continuous.

A member of the step lies in the identity combinator or in the diagonal function-space retract. The identity part lies in the Scott union at the empty finite set. The function-space part lies in the Scott union of the diagonal, which is Scott continuous, and each such piece remains in the corresponding disjunct. Conversely, a Scott-union witness is either already in the identity, or lies in the diagonal and is lifted by monotonicity of the diagonal.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.arrowR_diag_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem selfArrowStep_isScottContinuous :
    IsScottContinuous selfArrowStep := by
  constructor
  intro a
  have h := arrowR_diag_isScottContinuous.out a
  ext k
  constructor
  · intro hk
    rcases hk with hk | hk
    · exact mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inl hk⟩
    · have : k ∈ scottUnion (fun a => arrowR a a) a := by rwa [← h]
      obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp this
      exact mem_scottUnion.mpr ⟨n, hn, Or.inr hkn⟩
  · intro hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
    rcases hkn with hkn | hkn
    · exact Or.inl hkn
    · exact Or.inr (isScottContinuous_monotone arrowR_diag_isScottContinuous hn hkn)

end DomainTheory.DataTypesAsLattices
