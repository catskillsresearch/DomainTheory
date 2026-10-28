module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Retracts.Fixpoints
public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Graph.theorem_1_2
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Closures.Closure
public import DomainTheory.DataTypesAsLattices.FixedLattices.IsCompact
public import DomainTheory.DataTypesAsLattices.Retracts.retractBasis
public import DomainTheory.DataTypesAsLattices.Retracts.vals
public import DomainTheory.DataTypesAsLattices.Retracts.IsCompactSubset
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more
public import DomainTheory.DataTypesAsLattices.Closures.closure_expansive
public import DomainTheory.DataTypesAsLattices.Closures.directed_finite_cover_subset

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def closureCompact (a : Pomega) (ha : Closure a) (n : ℕ) :
    Fixpoints (funOf a) :=
  ⟨funOf a (e n), by
    have hcont : IsScottContinuous (fun y => funOf a (funOf a y)) :=
      theorem_1_3 (funOf.isScottContinuous a) (funOf.isScottContinuous a)
    have hbeta := (theorem_1_2 hcont (comp a a)).1
    have h := congrArg (fun u => funOf u (e n)) ha.out.2.out
    have hcomp : funOf (comp a a) (e n) = funOf a (funOf a (e n)) :=
      congrArg (fun f => f (e n)) hbeta
    exact hcomp.symm.trans h.symm⟩

namespace closureCompact

theorem isCompact {a : Pomega} (ha : Closure a) (n : ℕ) :
    IsCompact (closureCompact a ha n) := by
  apply retractBasis.wayBelow ha.out.2
  exact ⟨n, closure_expansive ha (e n), rfl⟩

theorem isCompactSubset {a : Pomega} (ha : Closure a)
    (n : ℕ) : IsCompactSubset (closureCompact a ha n) := by
  intro s hs hsub
  have hen : e n ⊆ ⋃₀ (Subtype.val '' s) :=
    (closure_expansive ha (e n)).trans hsub
  obtain ⟨z, hz, hnz⟩ := directed_finite_cover_subset hs (e_finite n) hen
  refine ⟨z, hz, ?_⟩
  have := IsScottContinuous.monotone (funOf.isScottContinuous a) hnz
  rwa [z.property] at this

end closureCompact

end DomainTheory.DataTypesAsLattices
