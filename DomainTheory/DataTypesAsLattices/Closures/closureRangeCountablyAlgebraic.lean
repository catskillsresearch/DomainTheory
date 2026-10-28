module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts.Fixpoints
public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.FixedLattices.CountablyAlgebraic
public import DomainTheory.DataTypesAsLattices.FixedLattices.CountablyAlgebraicu2ecompact_finite_support
public import DomainTheory.DataTypesAsLattices.FixedLattices.IsCompact
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Closures.Closure
public import DomainTheory.DataTypesAsLattices.Closures.closureCompact
public import DomainTheory.DataTypesAsLattices.Closures.compact_fixed_iff
public import DomainTheory.DataTypesAsLattices.Closures.compactFixedBelow
public import DomainTheory.DataTypesAsLattices.Closures.fixed_eq_sSup_compacts
public import DomainTheory.DataTypesAsLattices.Retracts.vals

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def closureRangeCountablyAlgebraic (a : Pomega) (ha : Closure a) :
    CountablyAlgebraic (Fixpoints (funOf a)) where
  compact := closureCompact a ha
  compact_isCompact := closureCompact.isCompact ha
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
