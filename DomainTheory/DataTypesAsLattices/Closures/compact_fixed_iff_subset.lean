module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Closure
public import DomainTheory.DataTypesAsLattices.Closures.Isolated
public import DomainTheory.DataTypesAsLattices.Closures.squarePair
public import DomainTheory.DataTypesAsLattices.Closures.squareFst
public import DomainTheory.DataTypesAsLattices.Closures.squareSnd
public import DomainTheory.DataTypesAsLattices.Closures.boxTensor
public import DomainTheory.DataTypesAsLattices.Closures.boxTag
public import DomainTheory.DataTypesAsLattices.Closures.Vapply
public import DomainTheory.DataTypesAsLattices.Closures.closureCompact
public import DomainTheory.DataTypesAsLattices.Closures.compactFixedBelow
public import DomainTheory.DataTypesAsLattices.Closures.Vstep
public import DomainTheory.DataTypesAsLattices.Closures.VapplyY
public import DomainTheory.DataTypesAsLattices.Closures.closureRangeCountablyAlgebraic
public import DomainTheory.DataTypesAsLattices.Closures.representClosure
public import DomainTheory.DataTypesAsLattices.Closures.representClosureCode
public import DomainTheory.DataTypesAsLattices.Closures.representationEncode
public import DomainTheory.DataTypesAsLattices.Closures.representationDecode
public import DomainTheory.DataTypesAsLattices.Closures.representationOrderIso
public import DomainTheory.DataTypesAsLattices.Closures.Vcomb
public import DomainTheory.DataTypesAsLattices.Closures.selfArrowStep
public import DomainTheory.DataTypesAsLattices.Closures.dEq
public import DomainTheory.DataTypesAsLattices.Closures.closure_expansive
public import DomainTheory.DataTypesAsLattices.Closures.closureCompact_isCompact
public import DomainTheory.DataTypesAsLattices.Closures.compact_fixed_iff
public import DomainTheory.DataTypesAsLattices.Closures.retractBasis_eq_compactFixedBelow
public import DomainTheory.DataTypesAsLattices.Closures.fixed_eq_sSup_compacts
public import DomainTheory.DataTypesAsLattices.Closures.representClosure_mono
public import DomainTheory.DataTypesAsLattices.Closures.representClosure_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Closures.representClosureCode_app
public import DomainTheory.DataTypesAsLattices.Closures.representationDecode_encode
public import DomainTheory.DataTypesAsLattices.Closures.representationEncode_fixed
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
