module

public import DomainTheory.ContinuousLattice.MilnerCorrection
public import DomainTheory.ContinuousLattice.ScottMaps
public import DomainTheory.ContinuousLattice.Injective
public import Mathlib.Order.Preorder.Finite
import all Mathlib.Order.Preorder.Finite
public import DomainTheory.ContinuousLattice.Constructions.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Topology Set

variable {D : Type*} [CompleteLattice D]







/-- **Scott 1972, Theorem 2.12 (injectivity half, unconditional).** `Prop` is injective
(Sierpiński); the continuous-lattice half is now `isContinuousLattice_prop`. -/
theorem theorem_2_12_injective_half : IsInjectiveSpace Prop :=
  proposition_1_2

end DomainTheory.ContinuousLattice
