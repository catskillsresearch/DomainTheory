module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts.Fixpoints
public import DomainTheory.DataTypesAsLattices.Retracts.retractBasis
public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.FixedLattices.IsCompact
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Closures.Closure
public import DomainTheory.DataTypesAsLattices.Closures.closureCompact
public import DomainTheory.DataTypesAsLattices.Closures.compactFixedBelow
public import DomainTheory.DataTypesAsLattices.Retracts.vals
public import DomainTheory.DataTypesAsLattices.Retracts.IsCompactSubset
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more
public import DomainTheory.DataTypesAsLattices.Closures.compactFixedBelow_more
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
    have := IsScottContinuous.monotone (funOf.isScottContinuous a) hnx
    rwa [x.property] at this
  · rintro ⟨n, rfl⟩
    exact closureCompact.isCompact ha n

namespace compact_fixed_iff

theorem subset {a : Pomega} (ha : Closure a)
    (x : Fixpoints (funOf a)) :
    IsCompactSubset x ↔ ∃ n, x = closureCompact a ha n := by
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ :=
      hx (compactFixedBelow a x) (compactFixedBelow.directedSubset ha x)
        (le_of_eq (compactFixedBelow.sUnion ha x))
    obtain ⟨⟨n, hn⟩, hyx⟩ := hy
    have hyx' : (y : Pomega) ⊆ x := hyx
    have : y = x := Subtype.ext (subset_antisymm hyx' hxy)
    refine ⟨n, this.symm.trans (Subtype.ext hn)⟩
  · rintro ⟨n, rfl⟩
    exact closureCompact.isCompactSubset ha n

end compact_fixed_iff

end DomainTheory.DataTypesAsLattices
