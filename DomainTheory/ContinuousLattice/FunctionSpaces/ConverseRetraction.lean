module

public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import DomainTheory.ContinuousLattice.ScottMaps.PreservesDirectedSup

-- Namespace and map share the name `ConverseRetraction`.
set_option linter.dupNamespace false

@[expose] public section

universe u v

namespace DomainTheory.ContinuousLattice

open Set

variable {D : Type u} {D' : Type v}
variable [CompleteLattice D] [CompleteLattice D']

namespace ConverseRetraction

noncomputable def ConverseRetraction (i : D → D') (x' : D') : D :=
  sSup {x | i x ≤ x'}

theorem mono (i : D → D') : Monotone (ConverseRetraction i) := by
  intro a b hab
  exact sSup_le_sSup fun _ hx => le_trans hx hab

theorem preservesDirectedSup (i : D → D')
    (_hi : ∀ S : Set D, i (sSup S) = sSup (i '' S))
    (hwb : ∀ {x y : D}, x ≪ y → i x ≪ i y) (hD : ContinuousLattice D) :
    PreservesDirectedSup (ConverseRetraction i) := by
  intro S' hS'ne hS'dir
  apply le_antisymm
  · show sSup {x | i x ≤ sSup S'} ≤ sSup (ConverseRetraction i '' S')
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
    exact mono i (le_sSup hx'S')

end ConverseRetraction

end DomainTheory.ContinuousLattice
