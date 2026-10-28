module

public import DomainTheory.ContinuousLattice.WayBelow.WayBelow
public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import DomainTheory.ContinuousLattice.FunctionSpaces.IsContinuousLatticeProjection
public import DomainTheory.ContinuousLattice.FunctionSpaces.incl_converseRetr_le
public import DomainTheory.ContinuousLattice.FunctionSpaces.converseRetr_incl
public import DomainTheory.ContinuousLattice.FunctionSpaces.converseRetr_preservesDirectedSup
public import DomainTheory.ContinuousLattice.ScottMaps.continuous_of_preservesDirectedSup
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Finset.Basic

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

noncomputable def converseProjection
    (hi : ∀ S : Set D, i (sSup S) = sSup (i '' S)) (hinj : Function.Injective i)
    (hwb : ∀ {x y : D}, x ≪ y → i x ≪ i y) (hD : ContinuousLattice D) :
    IsContinuousLatticeProjection D D' where
  incl := ⟨i, continuous_of_preservesDirectedSup (fun _ _ _ => hi _)⟩
  retr := ⟨converseRetr i, continuous_of_preservesDirectedSup
    (converseRetr_preservesDirectedSup hi hwb hD)⟩
  retr_incl := fun d => converseRetr_incl hi hinj d
  incl_retr_le := fun x' => incl_converseRetr_le hi x'

end Proposition310

end DomainTheory.ContinuousLattice
