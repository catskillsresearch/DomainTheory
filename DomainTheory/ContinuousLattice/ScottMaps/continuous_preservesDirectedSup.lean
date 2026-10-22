module

public import DomainTheory.ContinuousLattice.Specialization
public import Mathlib.Order.ScottContinuity
public import Mathlib.Topology.Order.ScottTopology
public import DomainTheory.ContinuousLattice.ScottMaps.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set Topology

variable {D D' D'' : Type*} [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']


theorem continuous_preservesDirectedSup {f : D → D'}
    (hf : @Continuous D D' scottTopologicalSpace scottTopologicalSpace f) :
    PreservesDirectedSup f := by
  have hD : @IsScott D univ _ (Topology.scott D univ) :=
    @IsScott.mk D univ _ (Topology.scott D univ) rfl
  have hD' : @IsScott D' univ _ (Topology.scott D' univ) :=
    @IsScott.mk D' univ _ (Topology.scott D' univ) rfl
  have hsc : ScottContinuous f :=
    scottContinuousOn_univ.1 <|
      (@Topology.IsScott.scottContinuousOn_iff_continuous D D' _
        (Topology.scott D univ) _ (Topology.scott D' univ) hD' f univ hD
        (fun _ _ _ => trivial)).2 hf
  intro S hS hSdir
  exact (hsc hS hSdir (isLUB_sSup S)).sSup_eq.symm

end DomainTheory.ContinuousLattice
