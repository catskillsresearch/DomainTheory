module

public import DomainTheory.ContinuousLattice.WayBelow.WayBelow
public import DomainTheory.ContinuousLattice.ScottMaps.PreservesDirectedSup
public import DomainTheory.ContinuousLattice.FunctionSpaces.stepFun
public import DomainTheory.ContinuousLattice.FunctionSpaces.stepFun_of_not_wayBelow
public import DomainTheory.ContinuousLattice.FunctionSpaces.stepFun_of_wayBelow
public import Mathlib.Order.BourbakiWitt
public import DomainTheory.ContinuousLattice.WayBelow.scottOpen_wayBelow
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace


variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

/-- Step functions are Scott-continuous: `{x | e ≪ x}` is Scott-open, so the conditional commutes
with directed suprema. -/
theorem stepFun_preservesDirectedSup (e : D) (e' : D') :
    PreservesDirectedSup (stepFun e e') := by
  intro S hS hSdir
  show stepFun e e' (sSup S) = sSup (Set.image (stepFun e e') S)
  by_cases h : e ≪ sSup S
  · rw [stepFun_of_wayBelow h]
    obtain ⟨s, hsS, hes⟩ := (scottOpen_wayBelow e).2 hS hSdir h
    apply le_antisymm
    · refine le_sSup_of_le (Set.mem_image_of_mem _ hsS) ?_
      rw [stepFun_of_wayBelow hes]
    · refine sSup_le ?_
      rintro _ ⟨x, _, rfl⟩
      exact iSup_le fun _ => le_rfl
  · rw [stepFun_of_not_wayBelow h]
    refine (sSup_eq_bot.2 ?_).symm
    rintro _ ⟨x, hxS, rfl⟩
    refine stepFun_of_not_wayBelow (fun hex => ?_)
    exact h (hex.trans_le (le_sSup hxS))

end DomainTheory.ContinuousLattice
