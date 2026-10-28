module

public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import Mathlib.Order.CompleteLattice.Basic
public import DomainTheory.ContinuousLattice.Constructions.proposition_2_8
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Topology Set

variable {D : Type*} [CompleteLattice D]

theorem isContinuousLattice_prop : ContinuousLattice Prop :=
  proposition_2_8

end DomainTheory.ContinuousLattice
