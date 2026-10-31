module

public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMap
import DomainTheory.ContinuousLattice.ScottMaps.scottOpen_preimage

@[expose] public section

universe u v

namespace DomainTheory.ContinuousLattice

open Set Finset

variable {D : Type u} {D' : Type v}
variable [CompleteLattice D] [CompleteLattice D']

structure ContinuousLatticeRetraction (D : Type u) (D' : Type v)
    [CompleteLattice D] [CompleteLattice D'] where
  incl : ScottMap D D'
  retr : ScottMap D' D
  retr_incl : ∀ d, retr (incl d) = d

namespace ContinuousLatticeRetraction

theorem incl_preservesDirectedSup (R : ContinuousLatticeRetraction D D') :
    PreservesDirectedSup (R.incl : D → D') :=
  fun _ hS hSdir => R.incl.preservesDirectedSup_coe _ hS hSdir

theorem image_retr_wayBelow_directed (R : ContinuousLatticeRetraction D D') (d : D) :
    DirectedOn (· ≤ ·) (Set.image (R.retr : D' → D) {x' | x' ≪ R.incl d}) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  exact ⟨R.retr (a ⊔ b), ⟨a ⊔ b, WayBelow.sup ha hb, rfl⟩,
    R.retr.monotone le_sup_left, R.retr.monotone le_sup_right⟩

theorem image_retr_wayBelow_nonempty (R : ContinuousLatticeRetraction D D') (d : D) :
    (Set.image (R.retr : D' → D) {x' | x' ≪ R.incl d}).Nonempty :=
  ⟨R.retr ⊥, ⊥, WayBelow.bot _, rfl⟩

theorem sSup_image_retr_wayBelow (R : ContinuousLatticeRetraction D D') (hD' : ContinuousLattice D')
    (d : D) :
    sSup (Set.image (R.retr : D' → D) {x' | x' ≪ R.incl d}) = d := by
  have hne : ({x' : D' | x' ≪ R.incl d}).Nonempty := ⟨⊥, WayBelow.bot _⟩
  have hdir : DirectedOn (· ≤ ·) {x' : D' | x' ≪ R.incl d} := WayBelow.directedOn _
  rw [← R.retr.preservesDirectedSup_coe _ hne hdir, hD'.sSup_wayBelow (R.incl d), R.retr_incl d]

theorem retr_wayBelow_of_wayBelow_incl (R : ContinuousLatticeRetraction D D') {d : D} {x' : D'}
    (hx' : x' ≪ R.incl d) : R.retr x' ≪ d := by
  obtain ⟨U', hU'open, hd_in, hU'sub⟩ := hx'
  refine ⟨(R.incl : D → D') ⁻¹' U', scottOpen_preimage R.incl_preservesDirectedSup hU'open,
    hd_in, fun z hz => ?_⟩
  have hle : x' ≤ R.incl z := Set.mem_Ici.1 (hU'sub hz)
  have hjle := R.retr.monotone hle
  rw [R.retr_incl z] at hjle
  exact Set.mem_Ici.2 hjle

noncomputable def ambientSSup (R : ContinuousLatticeRetraction D D') (S : Set D) : D' :=
  sSup (Set.image (R.incl : D → D') S)

theorem retr_ambientSSup_eq_sSup (R : ContinuousLatticeRetraction D D') (S : Set D)
    (hS : S.Nonempty) (hdir : DirectedOn (· ≤ ·) S) :
    R.retr (ambientSSup R S) = sSup S := by
  unfold ambientSSup
  have hdir' : DirectedOn (· ≤ ·) (Set.image (R.incl : D → D') S) := by
    intro p hp q hq
    obtain ⟨a, ha, rfl⟩ := hp
    obtain ⟨b, hb, rfl⟩ := hq
    obtain ⟨c, hc, hac, hbc⟩ := hdir a ha b hb
    exact ⟨R.incl c, Set.mem_image_of_mem _ hc, R.incl.monotone hac, R.incl.monotone hbc⟩
  have hne' : (Set.image (R.incl : D → D') S).Nonempty := Set.image_nonempty.2 hS
  rw [R.retr.preservesDirectedSup_coe (Set.image (R.incl : D → D') S) hne' hdir']
  rw [Set.image_image, Set.image_congr fun a _ => R.retr_incl a]
  simp

end ContinuousLatticeRetraction

end DomainTheory.ContinuousLattice
