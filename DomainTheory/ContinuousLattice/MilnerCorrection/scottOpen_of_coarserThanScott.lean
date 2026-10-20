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
