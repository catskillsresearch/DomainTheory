module

public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import Mathlib.Data.Set.Finite.Powerset

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

def IsSigma11 (U : Set Pomega) : Prop :=
  ∃ f g, IsScottContinuous f ∧ IsScottContinuous g ∧
    U = {x | ∃ y, funOf (f x) y = funOf (g x) y}

end DomainTheory.DataTypesAsLattices
