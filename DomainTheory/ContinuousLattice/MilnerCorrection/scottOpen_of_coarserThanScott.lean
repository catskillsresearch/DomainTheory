/-ai
If a topology is coarser than the Scott topology, then every set open in it is Scott-open.

The inequality of topologies sends opens of the coarser topology to Scott-topology opens, and those are exactly the Scott-open sets.
ai-/
module

public import DomainTheory.ContinuousLattice.Specialization
public import DomainTheory.ContinuousLattice.MilnerCorrection.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set Topology

variable {D D' : Type*} [CompleteLattice D] [CompleteLattice D']






theorem scottOpen_of_coarserThanScott {τ : TopologicalSpace D} (hτ : CoarserThanScottTopology τ)
    {U : Set D} (hU : @IsOpen D τ U) : ScottOpen U :=
  isOpen_iff_scottOpen.mp (hτ U hU)

end DomainTheory.ContinuousLattice
