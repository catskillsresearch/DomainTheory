/-ai
Continuous-lattice interpolation: a set typed by a retract equals the union of the values of the retract on those finite sets e n that are contained in the set. The retract hypothesis is not used.

Typing says the retract fixes the set, and Scott continuity rewrites that value as a Scott union. An element of the set therefore lies in the value on some finite set contained in it. An element of such a value lies in the value on the whole set by monotonicity, hence in the set.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- Continuous-lattice interpolation: `x = ⋃ { a(e n) | e n ⊆ x }`. -/
theorem retract_interpolation {a x : Pomega} (_ha : IsRetract a) (hx : typed x a) :
    x = ⋃ n, {k | e n ⊆ x ∧ k ∈ funOf a (e n)} := by
  have hx' : funOf a x = x := hx.symm
  have hsc := funOf_isScottContinuous a x
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
