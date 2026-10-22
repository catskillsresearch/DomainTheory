module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- Continuous-lattice interpolation: `x = ⋃ { a(e n) | e n ⊆ x }`. -/
theorem retract_interpolation {a x : Pomega} (_ha : Retract a) (hx : typed x a) :
    x = ⋃ n, {k | e n ⊆ x ∧ k ∈ funOf a (e n)} := by
  have hx' : funOf a x = x := hx.symm
  have hsc := (funOf_isScottContinuous a).out x
  apply subset_antisymm
  · intro k hk
    have : k ∈ funOf a x := by rwa [hx']
    have : k ∈ scottUnion (funOf a) x := by rwa [← hsc]
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp this
    exact Set.mem_iUnion.mpr ⟨n, hn, hkn⟩
  · intro k hk
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion.mp hk
    have : k ∈ funOf a x :=
      isScottContinuous_monotone (funOf_isScottContinuous a) hn hkn
    rwa [hx'] at this

end DomainTheory.DataTypesAsLattices
