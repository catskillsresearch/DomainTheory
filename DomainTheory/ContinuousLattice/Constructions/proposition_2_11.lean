/-ai
Every continuous lattice is an injective space under its Scott topology.

Given an embedding and a continuous map into the lattice, the canonical Scott extension of the map along the embedding is continuous and agrees with the map on the image of the embedding.
ai-/
module

public import DomainTheory.ContinuousLattice.MilnerCorrection
public import DomainTheory.ContinuousLattice.ScottMaps
public import DomainTheory.ContinuousLattice.Injective
public import Mathlib.Order.Preorder.Finite
public import DomainTheory.ContinuousLattice.Constructions.Basic
public import DomainTheory.ContinuousLattice.Constructions.scottExtend_eq_of_continuous
public import DomainTheory.ContinuousLattice.Constructions.scottExtend_continuous

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Topology Set

variable {D : Type*} [CompleteLattice D]


/-- **Scott 1972, Proposition 2.11.** Every continuous lattice is an injective space under its
induced (Scott) topology. The witness is `scottExtend`, which extends any continuous `f` along
any embedding `e` (`scottExtend_eq_of_continuous`) and is itself continuous
(`scottExtend_continuous`). -/
theorem proposition_2_11 {E : Type*} [CompleteLattice E] (hE : IsContinuousLattice E) :
    @InjectiveSpace E scottTopologicalSpace := by
  let : TopologicalSpace E := scottTopologicalSpace
  constructor
  intro X Y _ _ e he f
  exact ⟨⟨scottExtend e f, scottExtend_continuous hE e f⟩,
    fun x => scottExtend_eq_of_continuous hE e he f f.continuous x⟩

end DomainTheory.ContinuousLattice
