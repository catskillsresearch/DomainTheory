module


public import DomainTheory.ContinuousLattice.FunctionSpaces.ContinuousLatticeRetractionProjection

import DomainTheory.ContinuousLattice.ScottMaps.scottOpen_preimage
@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

universe u v

variable {D : Type u} {D' : Type v}
variable [CompleteLattice D] [CompleteLattice D']

theorem proposition_2_10 (R : ContinuousLatticeRetraction D D') (hD' : ContinuousLattice D') :
    ContinuousLattice D ∧
      (scottTopologicalSpace : TopologicalSpace D) =
        TopologicalSpace.induced (R.incl : D → D') scottTopologicalSpace := by
  constructor
  · refine { out := ?_ }
    intro d
    refine ⟨fun x hx => hx.le, fun b hb => ?_⟩
    rw [← R.sSup_image_retr_wayBelow hD' d]
    exact sSup_le fun _ ⟨x', hx', hxeq⟩ => hxeq ▸ hb (R.retr_wayBelow_of_wayBelow_incl hx')
  · apply le_antisymm
    · intro U hU
      rw [isOpen_induced_iff (t := scottTopologicalSpace)] at hU
      obtain ⟨V', hV'open, rfl⟩ := hU
      rw [ScottOpen.isOpen_iff] at hV'open ⊢
      exact scottOpen_preimage R.incl_preservesDirectedSup hV'open
    · intro U hU
      rw [ScottOpen.isOpen_iff] at hU
      rw [@isOpen_iff_forall_mem_open _
        (TopologicalSpace.induced (R.incl : D → D') scottTopologicalSpace)]
      intro d hd
      have hmem : sSup (Set.image (R.retr : D' → D) {x' | x' ≪ R.incl d}) ∈ U := by
        rw [R.sSup_image_retr_wayBelow hD' d]; exact hd
      obtain ⟨p, hp, hpU⟩ :=
        hU.2 (R.image_retr_wayBelow_nonempty d) (R.image_retr_wayBelow_directed d) hmem
      obtain ⟨x', hx', rfl⟩ := hp
      refine ⟨(R.incl : D → D') ⁻¹' {z' | x' ≪ z'}, fun z hz => ?_, ?_, hx'⟩
      · have hjle := R.retr.monotone (show x' ≤ R.incl z from (hz : x' ≪ R.incl z).le)
        rw [R.retr_incl z] at hjle
        exact hU.1 hjle hpU
      · rw [isOpen_induced_iff (t := scottTopologicalSpace)]
        exact ⟨{z' | x' ≪ z'}, ScottOpen.isOpen_iff.mpr (ScottOpen.wayBelow x'), rfl⟩

end DomainTheory.ContinuousLattice
