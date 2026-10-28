module

public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import Mathlib.Data.Set.Finite.Powerset

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

def BooleanMemE (U : Set Pomega) : Prop :=
  ∃ (f : Pomega → Pomega) (N : ℕ) (E : Set Pomega),
    IsScottContinuous f ∧
      (∀ x, f x ⊆ {m | m < N}) ∧
        E.Finite ∧ (∀ e ∈ E, e ⊆ {m | m < N}) ∧
          U = {x | f x ∈ E}

end DomainTheory.DataTypesAsLattices
