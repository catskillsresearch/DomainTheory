module
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import DomainTheory.ContinuousLattice.WayBelow.WayBelow
public import DomainTheory.ContinuousLattice.ScottMaps.PreservesDirectedSup
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Directed
public import Mathlib.Topology.Inseparable
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Order.ScottTopology
public import Mathlib.Order.DirSupClosed
public import Mathlib.Order.ScottContinuity
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order
public import Mathlib.Order.FixedPoints
public import Mathlib.Order.BourbakiWitt

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

noncomputable def stepFun (e : D) (e' : D') (x : D) : D' := ⨆ _ : e ≪ x, e'

namespace stepFun

theorem of_wayBelow {e : D} {e' : D'} {x : D} (h : e ≪ x) : stepFun e e' x = e' :=
  iSup_pos h

theorem of_not_wayBelow {e : D} {e' : D'} {x : D} (h : ¬ e ≪ x) :
    stepFun e e' x = ⊥ :=
  iSup_neg h

theorem preservesDirectedSup (e : D) (e' : D') :
    PreservesDirectedSup (stepFun e e') := by
  intro S hS hSdir
  show stepFun e e' (sSup S) = sSup (Set.image (stepFun e e') S)
  by_cases h : e ≪ sSup S
  · rw [of_wayBelow h]
    obtain ⟨s, hsS, hes⟩ := (ScottOpen.wayBelow e).2 hS hSdir h
    apply le_antisymm
    · refine le_sSup_of_le (Set.mem_image_of_mem _ hsS) ?_
      rw [of_wayBelow hes]
    · refine sSup_le ?_
      rintro _ ⟨x, _, rfl⟩
      exact iSup_le fun _ => le_rfl
  · rw [of_not_wayBelow h]
    refine (sSup_eq_bot.2 ?_).symm
    rintro _ ⟨x, hxS, rfl⟩
    refine of_not_wayBelow (fun hex => ?_)
    exact h (hex.trans_le (le_sSup hxS))

end stepFun

end DomainTheory.ContinuousLattice
