module
public import DomainTheory.ContinuousLattice.WayBelow.WayBelow
public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice

public import DomainTheory.ContinuousLattice.ScottMaps.PreservesDirectedSup
public import DomainTheory.ContinuousLattice.FunctionSpaces.converseRetr
public import DomainTheory.ContinuousLattice.FunctionSpaces.converseRetr_mono
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

/-- `j` is Scott-continuous (uses (i)+(iii) and continuity of `D`). For directed `S'`: monotonicity
gives `⊔ j''S' ⊑ j(⊔S')`; conversely if `i x ⊑ ⊔S'` then for every `z ≪ x` we have `i z ≪ i x ⊑ ⊔S'`,
so `i z ⊑ x'` for some `x' ∈ S'` (directedness), whence `z ⊑ j(x') ⊑ ⊔ j''S'`; continuity of `D`
then gives `x ⊑ ⊔ j''S'`. -/
theorem converseRetr_preservesDirectedSup
    (_hi : ∀ S : Set D, i (sSup S) = sSup (i '' S))
    (hwb : ∀ {x y : D}, x ≪ y → i x ≪ i y) (hD : ContinuousLattice D) :
    PreservesDirectedSup (converseRetr i) := by
  intro S' hS'ne hS'dir
  apply le_antisymm
  · show sSup {x | i x ≤ sSup S'} ≤ sSup (converseRetr i '' S')
    apply sSup_le
    intro x hx
    have hx' : i x ≤ sSup S' := hx
    rw [← hD.sSup_wayBelow x]
    apply sSup_le
    intro z hz
    have hiz : i z ≪ sSup S' := (hwb hz).trans_le hx'
    obtain ⟨x', hx'S', hzx'⟩ := (WayBelow.sSup_iff hS'ne hS'dir).1 hiz
    have hz_mem : z ∈ {x | i x ≤ x'} := hzx'.le
    exact le_trans (le_sSup hz_mem) (le_sSup ⟨x', hx'S', rfl⟩)
  · apply sSup_le
    rintro _ ⟨x', hx'S', rfl⟩
    exact converseRetr_mono i (le_sSup hx'S')

end Proposition310

end DomainTheory.ContinuousLattice
