/-ai
Revaluation along a fixed set is Scott continuous in the functional argument.

A value contributed by an index in the set lies in the application of the functional to the corresponding numeral, so continuity of application in the function argument supplies a Scott-union witness for the revaluation. Conversely, a Scott-union witness contains such an application, and monotonicity of that continuous application returns the value to the revaluation.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.funOf_isScottContinuous_left

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem seqFun_left_isScottContinuous (x : Pomega) :
    IsScottContinuous (fun u => seqFun u x) := by
  constructor
  intro u
  ext k
  constructor
  · intro hk
    obtain ⟨i, hi, hki⟩ := Set.mem_iUnion₂.mp hk
    have : k ∈ scottUnion (fun v => funOf v (ofNat i)) u := by
      rw [← (funOf_isScottContinuous_left (ofNat i)).out u]; exact hki
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp this
    exact mem_scottUnion.mpr ⟨n, hn, Set.mem_iUnion₂.mpr ⟨i, hi, hkn⟩⟩
  · intro hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
    obtain ⟨i, hi, hki⟩ := Set.mem_iUnion₂.mp hkn
    exact Set.mem_iUnion₂.mpr ⟨i, hi,
      isScottContinuous_monotone (funOf_isScottContinuous_left (ofNat i)) hn hki⟩

end DomainTheory.DataTypesAsLattices
