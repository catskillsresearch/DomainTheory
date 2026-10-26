module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts.Fixpoints
public import DomainTheory.DataTypesAsLattices.Retracts.retractBasis
public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Closures.Closure
public import DomainTheory.DataTypesAsLattices.Closures.closure_expansive
public import DomainTheory.DataTypesAsLattices.Closures.compactFixedBelow
public import DomainTheory.DataTypesAsLattices.Retracts.vals
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem retractBasis_eq_compactFixedBelow {a : Pomega} (ha : Closure a)
    (x : Fixpoints (funOf a)) :
    retractBasis a x = compactFixedBelow a x := by
  ext k
  constructor
  · rintro ⟨n, hnx, hkn⟩
    refine ⟨⟨n, hkn⟩, ?_⟩
    rw [hkn]
    have := IsScottContinuous.monotone (funOf.isScottContinuous a) hnx
    rwa [x.property] at this
  · rintro ⟨⟨n, hkn⟩, hkx⟩
    refine ⟨n, ?_, hkn⟩
    have hsub : funOf a (e n) ⊆ (x : Pomega) := by
      rwa [hkn] at hkx
    exact (closure_expansive ha (e n)).trans hsub

end DomainTheory.DataTypesAsLattices
