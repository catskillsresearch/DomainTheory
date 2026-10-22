module

public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import DomainTheory.ContinuousLattice.Injective.InjectiveSpace
public import DomainTheory.ContinuousLattice.Constructions.isContinuousLattice_prop
public import DomainTheory.ContinuousLattice.Injective.proposition_1_2
public import Mathlib.Topology.Order
public import Mathlib.Data.Set.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Topology Set

variable {D : Type*} [CompleteLattice D]


/-- The Sierpiński space `𝕆 = Prop` realizes the smallest case of Theorem 2.12: it is both
injective (1.2) and a continuous lattice (2.8). -/
theorem sierpinski_isInjective_and_isContinuousLattice :
    InjectiveSpace Prop ∧ ContinuousLattice Prop :=
  ⟨proposition_1_2, isContinuousLattice_prop⟩

end DomainTheory.ContinuousLattice
