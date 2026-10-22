/-ai
The product of a family of continuous lattices is a continuous lattice, and its Scott topology is the product of the Scott topologies of the factors.

The two claims are the order-theoretic and topological halves of Proposition 2.9.
ai-/
module

public import DomainTheory.ContinuousLattice.MilnerCorrection
public import DomainTheory.ContinuousLattice.ScottMaps
public import DomainTheory.ContinuousLattice.Injective
public import Mathlib.Order.Preorder.Finite
public import DomainTheory.ContinuousLattice.Constructions.Basic
public import DomainTheory.ContinuousLattice.Constructions.proposition_2_9_a
public import DomainTheory.ContinuousLattice.Constructions.proposition_2_9_b

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Topology Set

variable {D : Type*} [CompleteLattice D]


/-- **Scott 1972, Proposition 2.9 (full statement).** The product of a family of continuous lattices
is again a continuous lattice (`proposition_2_9_a`) whose Scott topology agrees with the product
topology (`proposition_2_9_b`). -/
theorem proposition_2_9 {ι : Type*} (E : ι → Type*) [∀ i, CompleteLattice (E i)]
    (hE : ∀ i, IsContinuousLattice (E i)) :
    IsContinuousLattice (∀ i, E i) ∧
      (scottTopologicalSpace : TopologicalSpace (∀ i, E i)) =
        @Pi.topologicalSpace ι E (fun _ => scottTopologicalSpace) :=
  ⟨proposition_2_9_a E hE, proposition_2_9_b E hE⟩

end DomainTheory.ContinuousLattice
