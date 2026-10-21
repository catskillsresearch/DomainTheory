/-ai
Scott 1976, (2.27): the distributive extension of primitive recursion agrees with the integer recursion on numerals.

At zero this is the zero case of the extension. At a successor, a member of the union lies at the unique index in the numeral, namely the successor itself, where the value is the recursive value, and conversely membership at that index is membership in the union.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.primRecHat_zero

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (2.27).** The distributive extension agrees with the
integer recursion on singletons. -/
theorem primRecHat_ofNat (a f : Pomega) : ∀ n,
    primRecHat a f (ofNat n) = primRecVal a f n
  | 0 => primRecHat_zero a f
  | n + 1 => by
    ext k
    constructor
    · intro hk
      obtain ⟨m, hm, hkm⟩ := Set.mem_iUnion₂.mp hk
      simp [ofNat] at hm; subst hm; simpa [primRecVal] using hkm
    · intro hk
      exact Set.mem_iUnion₂.mpr ⟨n + 1, rfl, hk⟩

end DomainTheory.DataTypesAsLattices
