module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.directed_finite_cover_subset

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


















theorem closureCompact_isCompactSubset {a : Pomega} (ha : IsClosure a)
    (n : ℕ) : IsCompactSubset (closureCompact a ha n) := by
  intro s hs hsub
  have hen : e n ⊆ ⋃₀ (Subtype.val '' s) :=
    (closure_expansive ha (e n)).trans hsub
  obtain ⟨z, hz, hnz⟩ := directed_finite_cover_subset hs (e_finite n) hen
  refine ⟨z, hz, ?_⟩
  have := isScottContinuous_monotone (funOf_isScottContinuous a) hnz
  rwa [z.property] at this

end DomainTheory.DataTypesAsLattices
