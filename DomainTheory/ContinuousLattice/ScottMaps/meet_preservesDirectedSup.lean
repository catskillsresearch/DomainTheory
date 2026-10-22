module

public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import DomainTheory.ContinuousLattice.WayBelow.wayBelow_sSup_iff
public import DomainTheory.ContinuousLattice.WayBelow.WayBelowu2ele
public import DomainTheory.ContinuousLattice.WayBelow.WayBelowu2etrans_le
public import DomainTheory.ContinuousLattice.WayBelow.IsContinuousLatticeu2esSup_wayBelow
public import DomainTheory.ContinuousLattice.ScottMaps.PreservesDirectedSup
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set Topology

variable {D D' D'' : Type*} [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']


theorem meet_preservesDirectedSup (x : D) (hD : ContinuousLattice D) :
    PreservesDirectedSup (fun z => x ⊓ z) := by
  intro S hS hSdir
  apply le_antisymm
  · have hle : sSup {t | t ≪ x ⊓ sSup S} ≤ sSup (Set.image (fun z => x ⊓ z) S) := by
      apply sSup_le
      intro t ht
      obtain ⟨w, hwS, ht_w⟩ := (wayBelow_sSup_iff hS hSdir).1 (ht.trans_le inf_le_right)
      have hmem : x ⊓ w ∈ Set.image (fun z : D => x ⊓ z) S :=
        Set.mem_image_of_mem (fun z => x ⊓ z) hwS
      have hbound : x ⊓ w ≤ sSup (Set.image (fun z => x ⊓ z) S) := le_sSup hmem
      exact (le_inf (ht.le.trans inf_le_left) ht_w.le).trans hbound
    dsimp only
    rw [← hD.sSup_wayBelow (x ⊓ sSup S)]
    exact hle
  · apply sSup_le
    intro z hz
    obtain ⟨w, hwS, rfl⟩ := hz
    exact inf_le_inf le_rfl (le_sSup hwS)

end DomainTheory.ContinuousLattice
