module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Closure
public import DomainTheory.DataTypesAsLattices.Closures.closureCompact
public import DomainTheory.DataTypesAsLattices.Closures.closureCompact_isCompact
public import DomainTheory.DataTypesAsLattices.Closures.compact_fixed_iff
public import DomainTheory.DataTypesAsLattices.Closures.compactFixedBelow
public import DomainTheory.DataTypesAsLattices.Closures.fixed_eq_sSup_compacts

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- Theorem 5.1 packaged as a concrete countably algebraic lattice. -/
def closureRangeCountablyAlgebraic (a : Pomega) (ha : Closure a) :
    CountablyAlgebraic (Fixpoints (funOf a)) where
  compact := closureCompact a ha
  compact_isCompact := closureCompact_isCompact ha
  compact_complete := fun x hx => (compact_fixed_iff ha x).mp hx
  density := fun x => by
    have hsets : {k | IsCompact k ∧ k ≤ x} = compactFixedBelow a x := by
      ext k
      constructor
      · intro ⟨hk, hkx⟩
        obtain ⟨n, hn⟩ := (compact_fixed_iff ha k).mp hk
        exact ⟨⟨n, congrArg Subtype.val hn⟩, hkx⟩
      · intro ⟨⟨n, hn⟩, hkx⟩
        exact ⟨(compact_fixed_iff ha k).mpr ⟨n, Subtype.ext hn⟩, hkx⟩
    rw [hsets]
    exact (fixed_eq_sSup_compacts ha x).2

end DomainTheory.DataTypesAsLattices
