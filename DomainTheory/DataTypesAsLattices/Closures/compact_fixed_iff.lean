module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.IsClosure
public import DomainTheory.DataTypesAsLattices.Closures.closureCompact
public import DomainTheory.DataTypesAsLattices.Closures.closureCompact_isCompact

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

theorem compact_fixed_iff {a : Pomega} (ha : IsClosure a)
    (x : Fixpoints (funOf a)) :
    IsCompact x ↔ ∃ n, x = closureCompact a ha n := by
  constructor
  · intro hx
    have hdir := retractBasis_directed ha.2 x
    obtain ⟨y, hy, hxy⟩ :=
      hx (retractBasis a x) hdir (le_of_eq (retractBasis_sSup ha.2 x))
    obtain ⟨n, hnx, hyn⟩ := hy
    have hyc : y = closureCompact a ha n := by
      apply Subtype.ext
      exact hyn
    subst y
    refine ⟨n, le_antisymm hxy ?_⟩
    change funOf a (e n) ⊆ (x : Pomega)
    have := isScottContinuous_monotone (funOf_isScottContinuous a) hnx
    rwa [x.property] at this
  · rintro ⟨n, rfl⟩
    exact closureCompact_isCompact ha n

end DomainTheory.DataTypesAsLattices
