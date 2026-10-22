/-ai
From a map i that preserves arbitrary suprema, is injective, and preserves the way-below relation, on a continuous lattice, one assembles the continuous-lattice projection whose inclusion is i and whose retraction is Scott's candidate j(x') = ⊔ {x | i(x) ≤ x'}. Preservation of arbitrary suprema gives preservation of directed suprema for i, the candidate retraction preserves directed suprema, the retraction after the inclusion is the identity, and the inclusion after the retraction lies below the identity.
ai-/
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
public import DomainTheory.ContinuousLattice.FunctionSpaces.incl_converseRetr_le
public import DomainTheory.ContinuousLattice.FunctionSpaces.converseRetr_incl
public import DomainTheory.ContinuousLattice.FunctionSpaces.converseRetr_preservesDirectedSup

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

/-- The projection assembled from a map `i` satisfying 3.10(i)–(iii). -/
noncomputable def converseProjection
    (hi : ∀ S : Set D, i (sSup S) = sSup (i '' S)) (hinj : Function.Injective i)
    (hwb : ∀ {x y : D}, x ≪ y → i x ≪ i y) (hD : IsContinuousLattice D) :
    IsContinuousLatticeProjection D D' where
  incl := ⟨i, continuous_of_preservesDirectedSup (fun _ _ _ => hi _)⟩
  retr := ⟨converseRetr i, continuous_of_preservesDirectedSup
    (converseRetr_preservesDirectedSup hi hwb hD)⟩
  retr_incl := fun d => converseRetr_incl hi hinj d
  incl_retr_le := fun x' => incl_converseRetr_le hi x'

end Proposition310

end DomainTheory.ContinuousLattice
