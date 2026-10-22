/-ai
The Sierpiński space of propositions is both an injective space and a continuous lattice.

Injectivity is Proposition 1.2, and continuity is the theorem that the two-point lattice is a continuous lattice.
ai-/
module

public import DomainTheory.ContinuousLattice.MilnerCorrection
public import DomainTheory.ContinuousLattice.ScottMaps
public import DomainTheory.ContinuousLattice.Injective
public import Mathlib.Order.Preorder.Finite
public import DomainTheory.ContinuousLattice.Constructions.Basic
public import DomainTheory.ContinuousLattice.Constructions.isContinuousLattice_prop

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
