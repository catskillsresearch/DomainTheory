module

public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import DomainTheory.ContinuousLattice.Specialization.scottTopologicalSpace
public import DomainTheory.ContinuousLattice.Injective.InjectiveSpace
public import DomainTheory.ContinuousLattice.Constructions.proposition_2_11
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Topology Set

variable {D : Type*} [CompleteLattice D]


/-- **Scott 1972, Theorem 2.12 (forward direction).** Every continuous lattice is an injective
space under its Scott topology. This is the substantial half of the equivalence "injective
spaces = continuous lattices", and is exactly Proposition 2.11. -/
theorem theorem_2_12_forward {E : Type*} [CompleteLattice E] (hE : ContinuousLattice E) :
    @InjectiveSpace E scottTopologicalSpace :=
  proposition_2_11 hE

end DomainTheory.ContinuousLattice
