module

public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import DomainTheory.ContinuousLattice.Injective.InjectiveSpace
public import DomainTheory.ContinuousLattice.Injective.proposition_1_2
public import Mathlib.Topology.Order
public import Mathlib.Data.Set.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Topology Set

variable {D : Type*} [CompleteLattice D]


/-- **Scott 1972, Theorem 2.12 (backward, Sierpiński base case).** `Prop` is a continuous
lattice (`isContinuousLattice_prop`), so its injectivity (Proposition 1.2) is an instance of the
equivalence. -/
theorem theorem_2_12_sierpinski_backward (_h : ContinuousLattice Prop) : InjectiveSpace Prop :=
  proposition_1_2

end DomainTheory.ContinuousLattice
