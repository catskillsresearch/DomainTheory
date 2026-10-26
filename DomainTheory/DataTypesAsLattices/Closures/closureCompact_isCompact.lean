module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts.retractBasis
public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.FixedLattices.IsCompact
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Closures.Closure
public import DomainTheory.DataTypesAsLattices.Closures.closureCompact
public import DomainTheory.DataTypesAsLattices.Closures.closure_expansive

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem closureCompact_isCompact {a : Pomega} (ha : Closure a) (n : ℕ) :
    IsCompact (closureCompact a ha n) := by
  apply retractBasis.wayBelow ha.out.2
  exact ⟨n, closure_expansive ha (e n), rfl⟩

end DomainTheory.DataTypesAsLattices
