module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Closures.union_left_isScottContinuous

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem union_const_left_isScottContinuous (c : Pomega) :
    IsScottContinuous (fun x => c ∪ x) := by
  have : (fun x : Pomega => c ∪ x) = (fun x => x ∪ c) := by
    funext x; exact Set.union_comm c x
  rw [this]
  exact union_left_isScottContinuous c

end DomainTheory.DataTypesAsLattices
