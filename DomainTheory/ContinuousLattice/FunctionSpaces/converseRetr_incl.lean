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
public import DomainTheory.ContinuousLattice.FunctionSpaces.BasicInst30
public import DomainTheory.ContinuousLattice.FunctionSpaces.BasicInst33
public import DomainTheory.ContinuousLattice.FunctionSpaces.idMap_apply
public import DomainTheory.ContinuousLattice.FunctionSpaces.comp_apply
public import DomainTheory.ContinuousLattice.FunctionSpaces.const_apply
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottLambda_apply
public import DomainTheory.ContinuousLattice.FunctionSpaces.converseRetr
public import DomainTheory.ContinuousLattice.FunctionSpaces.incl_mono_of_preservesSSup
public import DomainTheory.ContinuousLattice.FunctionSpaces.le_of_incl_le

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace


variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

section Proposition310

open Finset

variable {i : D → D'}

/-- `j ∘ i = id` (uses (i)+(ii)): `{x | i x ⊑ i y} = Iic y`, whose join is `y`. -/
theorem converseRetr_incl (hi : ∀ S : Set D, i (sSup S) = sSup (i '' S))
    (hinj : Function.Injective i) (y : D) : converseRetr i (i y) = y := by
  have hset : {x | i x ≤ i y} = Set.Iic y := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_Iic]
    exact ⟨le_of_incl_le hi hinj, fun hx => incl_mono_of_preservesSSup hi hx⟩
  show sSup {x | i x ≤ i y} = y
  rw [hset]
  exact le_antisymm (sSup_le fun _ hx => hx) (le_sSup le_rfl)

end Proposition310

end DomainTheory.ContinuousLattice
