module

public import DomainTheory.ContinuousLattice.FunctionSpaces.converseRetr
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

theorem incl_converseRetr_le (hi : ∀ S : Set D, i (sSup S) = sSup (i '' S)) (x' : D') :
    i (converseRetr i x') ≤ x' := by
  show i (sSup {x | i x ≤ x'}) ≤ x'
  rw [hi]
  exact sSup_le (by rintro _ ⟨x, hx, rfl⟩; exact hx)

end Proposition310

end DomainTheory.ContinuousLattice
