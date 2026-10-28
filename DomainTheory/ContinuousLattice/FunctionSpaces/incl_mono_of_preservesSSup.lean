module
public import DomainTheory.ContinuousLattice.FunctionSpaces.incl_sup_of_preservesSSup
public import Mathlib.Order.BourbakiWitt
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
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

theorem incl_mono_of_preservesSSup (hi : ∀ S : Set D, i (sSup S) = sSup (i '' S)) :
    Monotone i := by
  intro x y hxy
  have h := incl_sup_of_preservesSSup hi x y
  rw [sup_eq_right.mpr hxy] at h
  rw [h]; exact le_sup_left

end Proposition310

end DomainTheory.ContinuousLattice
