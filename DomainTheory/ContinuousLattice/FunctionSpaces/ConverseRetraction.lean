module

public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import DomainTheory.ContinuousLattice.ScottMaps.PreservesDirectedSup
public import DomainTheory.ContinuousLattice.FunctionSpaces.ContinuousLatticeProjection

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

theorem incl_converseRetr_le (i : D → D') (hi : ∀ S : Set D, i (sSup S) = sSup (i '' S))
    (x' : D') :
    i (ConverseRetraction i x') ≤ x' := by
  show i (sSup {x | i x ≤ x'}) ≤ x'
  rw [hi]
  exact sSup_le (by rintro _ ⟨x, hx, rfl⟩; exact hx)

theorem converseRetr_incl (i : D → D') (hi : ∀ S : Set D, i (sSup S) = sSup (i '' S))
    (hinj : Function.Injective i) (y : D) :
    ConverseRetraction i (i y) = y := by
  have hset : {x | i x ≤ i y} = Set.Iic y := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_Iic]
    exact ⟨ContinuousLatticeProjection.le_of_incl_le i hi hinj,
      fun hx => ContinuousLatticeProjection.incl_mono_of_preservesSSup i hi hx⟩
  show sSup {x | i x ≤ i y} = y
  rw [hset]
  exact le_antisymm (sSup_le fun _ hx => hx) (le_sSup le_rfl)

end ConverseRetraction

end DomainTheory.ContinuousLattice
