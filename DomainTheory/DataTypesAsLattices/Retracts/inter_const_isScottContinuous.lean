/-ai
Intersection with a fixed set preserves Scott continuity.

Compare membership of an index in the two sides of the continuity equation. If the index lies in the value of the continuous map and in the fixed set, continuity puts it in the Scott union, so some finite set e n contained in the argument carries it, and it remains in the intersection. Conversely, membership in the Scott union of the intersected map supplies such a finite set together with membership in the fixed set, and monotonicity of the continuous map returns the index to the value.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem inter_const_isScottContinuous {f : Pomega → Pomega}
    (hf : IsScottContinuous f) (b : Pomega) :
    IsScottContinuous (fun z => f z ∩ b) := by
  constructor
  intro x
  ext k
  constructor
  · intro ⟨hkf, hkb⟩
    have : k ∈ scottUnion f x := by rwa [← hf.out x]
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp this
    exact mem_scottUnion.mpr ⟨n, hn, hkn, hkb⟩
  · intro hk
    obtain ⟨n, hn, hkn, hkb⟩ := mem_scottUnion.mp hk
    exact ⟨isScottContinuous_monotone hf hn hkn, hkb⟩

end DomainTheory.DataTypesAsLattices
