/-ai
The distributive extension of primitive recursion at the numeral zero equals the base value.

A member of the union lies at the unique index in the numeral zero, where the primitive-recursive value is the base, and conversely membership in the base is membership at index zero.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices















































theorem primRecHat_zero (a f : Pomega) : primRecHat a f (ofNat 0) = a := by
  ext k
  constructor
  · intro hk
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion₂.mp hk
    simp [ofNat] at hn; subst hn; simpa [primRecVal] using hkn
  · intro hk
    exact Set.mem_iUnion₂.mpr ⟨0, rfl, hk⟩

end DomainTheory.DataTypesAsLattices
