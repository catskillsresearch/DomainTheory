
module

public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import Mathlib.Data.Set.Finite.Powerset

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

def uvU (x y : Pomega) : Pomega :=
  {k | (k = 0 ∧ (x.Nonempty ∨ y.Nonempty)) ∨
       (k = 1 ∧ ((0 ∈ x ∧ ∃ n, n + 1 ∈ y) ∨ ((∃ n, n + 1 ∈ x) ∧ 0 ∈ y)))}

end DomainTheory.DataTypesAsLattices
