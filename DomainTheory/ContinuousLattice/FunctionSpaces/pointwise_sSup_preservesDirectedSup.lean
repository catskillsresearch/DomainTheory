module

public import DomainTheory.ContinuousLattice.ScottMaps
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.FixedPoints
public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMap
public import DomainTheory.ContinuousLattice.FunctionSpaces.comp
public import DomainTheory.ContinuousLattice.FunctionSpaces.monotone
public import DomainTheory.ContinuousLattice.FunctionSpaces.IsContinuousLatticeRetraction
public import DomainTheory.ContinuousLattice.FunctionSpaces.IsContinuousLatticeProjection
public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMapRetraction
public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMapProjection
public import DomainTheory.ContinuousLattice.FunctionSpaces.preservesDirectedSup_coe

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace


variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

namespace ScottMap

theorem pointwise_sSup_preservesDirectedSup (F : Set (ScottMap D D')) :
    PreservesDirectedSup (fun x => sSup (Set.image (fun f : ScottMap D D' => (f : D → D') x) F)) := by
  intro S hS hSdir
  set H := fun x => sSup (Set.image (fun f : ScottMap D D' => (f : D → D') x) F)
  show H (sSup S) = sSup (Set.image H S)
  apply le_antisymm
  · apply sSup_le
    intro b hb
    obtain ⟨f, hfF, rfl⟩ := hb
    change f (sSup S) ≤ sSup (Set.image H S)
    rw [f.preservesDirectedSup_coe S hS hSdir]
    apply sSup_le
    intro c hc
    obtain ⟨s, hsS, rfl⟩ := hc
    exact le_trans (le_sSup (Set.mem_image_of_mem (fun g : ScottMap D D' => (g : D → D') s) hfF))
      (le_sSup (Set.mem_image_of_mem H hsS))
  · apply sSup_le
    intro b hb
    obtain ⟨s, hsS, rfl⟩ := hb
    apply sSup_le
    intro c hc
    obtain ⟨f, hfF, rfl⟩ := hc
    exact le_trans (ScottMap.monotone f (le_sSup hsS))
      (le_sSup (Set.mem_image_of_mem (fun g : ScottMap D D' => (g : D → D') (sSup S)) hfF))

end ScottMap

end DomainTheory.ContinuousLattice
