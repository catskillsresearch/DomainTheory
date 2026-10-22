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


/-- The Sierpiński space `Prop` (Scott's `𝕆`) is a continuous lattice: it is a finite complete
lattice, so Proposition 2.8 applies. -/
theorem isContinuousLattice_prop : ContinuousLattice Prop :=
  proposition_2_8

end DomainTheory.ContinuousLattice
