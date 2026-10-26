module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Closure
public import DomainTheory.DataTypesAsLattices.Closures.closureCompact
public import DomainTheory.DataTypesAsLattices.Closures.closureCompact_isCompact

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem compact_fixed_iff {a : Pomega} (ha : Closure a)
    (x : Fixpoints (funOf a)) :
    IsCompact x ↔ ∃ n, x = closureCompact a ha n := by
  constructor
  · intro hx
    have hdir := retractBasis.directed ha.out.2 x
    obtain ⟨y, hy, hxy⟩ :=
      hx (retractBasis a x) hdir (le_of_eq (retractBasis.eq_sSup ha.out.2 x))
    obtain ⟨n, hnx, hyn⟩ := hy
    have hyc : y = closureCompact a ha n := by
      apply Subtype.ext
      exact hyn
    subst y
    refine ⟨n, le_antisymm hxy ?_⟩
    change funOf a (e n) ⊆ (x : Pomega)
    have := IsScottContinuous.monotone (funOf_isScottContinuous a) hnx
    rwa [x.property] at this
  · rintro ⟨n, rfl⟩
    exact closureCompact_isCompact ha n

end DomainTheory.DataTypesAsLattices
