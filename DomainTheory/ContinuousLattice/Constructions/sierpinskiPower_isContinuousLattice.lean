/-ai
Any power of the two-point lattice is a continuous lattice.

The two-point lattice is a continuous lattice, and a product of continuous lattices is a continuous lattice.
ai-/
module

public import DomainTheory.ContinuousLattice.MilnerCorrection
public import DomainTheory.ContinuousLattice.ScottMaps
public import DomainTheory.ContinuousLattice.Injective
public import Mathlib.Order.Preorder.Finite
public import DomainTheory.ContinuousLattice.Constructions.Basic
public import DomainTheory.ContinuousLattice.Constructions.proposition_2_9_a
public import DomainTheory.ContinuousLattice.Constructions.isContinuousLattice_prop

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Topology Set

variable {D : Type*} [CompleteLattice D]


/-- A power of Scott's two-point space `𝕆 = Prop` is a continuous lattice: `Prop` is a continuous
lattice (`isContinuousLattice_prop`) and products of continuous lattices are continuous
(Proposition 2.9(a)). This is the order-theoretic content of "a Cartesian power of `𝕆` is a
continuous lattice", the construction Theorem 2.12 retracts onto. -/
theorem sierpinskiPower_isContinuousLattice (ι : Type*) : ContinuousLattice (ι → Prop) :=
  proposition_2_9_a (fun _ => Prop) (fun _ => isContinuousLattice_prop)

end DomainTheory.ContinuousLattice
