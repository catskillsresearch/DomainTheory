module

public import DomainTheory.ContinuousLattice.Injective.InjectiveSpace
public import DomainTheory.ContinuousLattice.Injective.proposition_1_2
public import Mathlib.Topology.Order
public import Mathlib.Data.Set.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Topology Set

variable {D : Type*} [CompleteLattice D]


/-- **Scott 1972, Theorem 2.12 (injectivity half, unconditional).** `Prop` is injective
(Sierpiński); the continuous-lattice half is now `isContinuousLattice_prop`. -/
theorem theorem_2_12_injective_half : InjectiveSpace Prop :=
  proposition_1_2

end DomainTheory.ContinuousLattice
