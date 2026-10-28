module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts.Fixpoints
public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.FixedLattices.CountablyAlgebraic
public import DomainTheory.DataTypesAsLattices.FixedLattices.CountablyAlgebraicu2ecompact_finite_support
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Closures.Closure
public import DomainTheory.DataTypesAsLattices.Closures.representClosure
public import DomainTheory.DataTypesAsLattices.Closures.representClosureCode
public import DomainTheory.DataTypesAsLattices.Closures.representationOrderIso
public import DomainTheory.DataTypesAsLattices.Retracts.vals
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem theorem_5_2 {α : Type u} [CompleteLattice α]
    (D : CountablyAlgebraic α) :
    IsScottContinuous (representClosure D) ∧
      Closure (representClosureCode D) ∧
      ∃ φ : α → Fixpoints (funOf (representClosureCode D)),
        Function.Bijective φ ∧
          ∀ x y, x ≤ y ↔ (φ x : Pomega) ⊆ φ y :=
  ⟨representClosure.isScottContinuous D,
    representClosureCode.isClosure D,
    ⟨fun x => representationOrderIso D x,
      (representationOrderIso D).toEquiv.bijective,
      fun x y => by
        constructor
        · intro hxy
          exact (representationOrderIso D).map_rel_iff.mpr hxy
        · intro hsub
          exact (representationOrderIso D).map_rel_iff.mp hsub⟩⟩

end DomainTheory.DataTypesAsLattices
