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
public import DomainTheory.ContinuousLattice.FunctionSpaces.BasicInst28
public import DomainTheory.ContinuousLattice.FunctionSpaces.le_def
public import DomainTheory.ContinuousLattice.FunctionSpaces.BasicInst30
public import DomainTheory.ContinuousLattice.FunctionSpaces.BasicInst33
public import DomainTheory.ContinuousLattice.FunctionSpaces.idMap_apply
public import DomainTheory.ContinuousLattice.FunctionSpaces.comp_apply
public import DomainTheory.ContinuousLattice.FunctionSpaces.const_apply
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottLambda_apply
public import DomainTheory.ContinuousLattice.FunctionSpaces.IsProjection

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace


variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

section Projections

/-- Pointwise characterization of projections: idempotent and deflationary. -/
theorem isProjection_iff {j : ScottMap D D} :
    IsProjection j ↔ (∀ x, (j : D → D) (j x) = j x) ∧ (∀ x, (j : D → D) x ≤ x) := by
  constructor
  · rintro ⟨hidem, hle⟩
    refine ⟨fun x => ?_, fun x => ?_⟩
    · have h : ((j.comp j : ScottMap D D) : D → D) x = (j : D → D) x := by rw [hidem]
      rwa [ScottMap.comp_apply] at h
    · have h := (ScottMap.le_def.mp hle) x
      rwa [ScottMap.idMap_apply] at h
  · rintro ⟨hidem, hle⟩
    exact ⟨ScottMap.ext fun x => by rw [ScottMap.comp_apply]; exact hidem x,
      ScottMap.le_def.mpr fun x => by rw [ScottMap.idMap_apply]; exact hle x⟩

end Projections

end DomainTheory.ContinuousLattice
