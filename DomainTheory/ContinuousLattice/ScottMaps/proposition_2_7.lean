module

public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import DomainTheory.ContinuousLattice.Specialization.scottTopologicalSpace
public import DomainTheory.ContinuousLattice.ScottMaps.continuous_of_preservesDirectedSup
public import DomainTheory.ContinuousLattice.ScottMaps.meet_preservesDirectedSup
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology

variable {D D' D'' : Type*} [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

namespace proposition_2_7

theorem sup :
    @Continuous (D × D) D scottTopologicalSpace scottTopologicalSpace (fun p : D × D => p.1 ⊔ p.2) :=
  continuous_of_preservesDirectedSup <| by
    intro S hS hSdir
    simpa using (ScottContinuous.sup₂ (β := D) (d := S) hS hSdir (isLUB_sSup S)).sSup_eq.symm

theorem inf_left (hD : ContinuousLattice D) (y : D) :
    @Continuous D D scottTopologicalSpace scottTopologicalSpace (fun x => x ⊓ y) :=
  continuous_of_preservesDirectedSup <| by
    intro S' hS' hSdir'
    rw [show (fun x => x ⊓ y) = fun z => y ⊓ z from funext fun x => inf_comm x y]
    have h := meet_preservesDirectedSup y hD
    exact h (S := S') hS' hSdir'

theorem inf_right (hD : ContinuousLattice D) (x : D) :
    @Continuous D D scottTopologicalSpace scottTopologicalSpace (fun y => x ⊓ y) :=
  continuous_of_preservesDirectedSup (meet_preservesDirectedSup x hD)

end proposition_2_7

end DomainTheory.ContinuousLattice
