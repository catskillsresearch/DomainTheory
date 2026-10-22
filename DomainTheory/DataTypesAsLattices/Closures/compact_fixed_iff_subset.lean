module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.compactFixedBelow_directedSubset
public import DomainTheory.DataTypesAsLattices.Closures.compactFixedBelow_sUnion
public import DomainTheory.DataTypesAsLattices.Closures.closureCompact_isCompactSubset

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem compact_fixed_iff_subset {a : Pomega} (ha : Closure a)
    (x : Fixpoints (funOf a)) :
    IsCompactSubset x ↔ ∃ n, x = closureCompact a ha n := by
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ :=
      hx (compactFixedBelow a x) (compactFixedBelow_directedSubset ha x)
        (le_of_eq (compactFixedBelow_sUnion ha x))
    obtain ⟨⟨n, hn⟩, hyx⟩ := hy
    have hyx' : (y : Pomega) ⊆ x := hyx
    have : y = x := Subtype.ext (subset_antisymm hyx' hxy)
    refine ⟨n, this.symm.trans (Subtype.ext hn)⟩
  · rintro ⟨n, rfl⟩
    exact closureCompact_isCompactSubset ha n

end DomainTheory.DataTypesAsLattices
