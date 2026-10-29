module

public import DomainTheory.ContinuousLattice.FunctionSpaces.IsContinuousLatticeRetraction
public import DomainTheory.ContinuousLattice.FunctionSpaces.proposition_2_10
public import DomainTheory.ContinuousLattice.ScottMaps.continuous_of_preservesDirectedSup
public import DomainTheory.ContinuousLattice.ScottMaps.preservesDirectedSup_monotone
public import DomainTheory.ContinuousLattice.Specialization.scottTopologicalSpace
public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import Mathlib.Order.BourbakiWitt
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Topology Set

variable {L : Type*} [CompleteLattice L]

abbrev IdemFix (e : L → L) : Type _ := {x : L // e x = x}

namespace IdemFix

variable {e : L → L}

@[reducible] noncomputable def supSet (hidem : ∀ x, e (e x) = e x) : SupSet (IdemFix e) :=
  ⟨fun S => ⟨e (sSup (Subtype.val '' S)), hidem _⟩⟩

theorem isLUB_sSup (hidem : ∀ x, e (e x) = e x) (hmono : Monotone e) :
    letI := supSet hidem
    ∀ S : Set (IdemFix e), IsLUB S (sSup S) := by
  let := supSet hidem
  intro S
  constructor
  · intro k hk
    rw [Subtype.coe_le_coe.symm, Subtype.coe_mk]
    show (k : L) ≤ e (sSup (Subtype.val '' S))
    calc (k : L) = e k := k.2.symm
      _ ≤ e (sSup (Subtype.val '' S)) :=
          hmono (le_sSup (Set.mem_image_of_mem _ hk))
  · intro w hw
    rw [Subtype.coe_le_coe.symm, Subtype.coe_mk]
    show e (sSup (Subtype.val '' S)) ≤ (w : L)
    calc e (sSup (Subtype.val '' S)) ≤ e (w : L) := by
          refine hmono (sSup_le ?_)
          rintro _ ⟨k, hk, rfl⟩
          exact hw hk
      _ = (w : L) := w.2

@[reducible] noncomputable def completeLattice (hidem : ∀ x, e (e x) = e x) (hmono : Monotone e) :
    CompleteLattice (IdemFix e) :=
  letI := supSet hidem
  completeLatticeOfSup (IdemFix e) (isLUB_sSup hidem hmono)

theorem coe_sSup (hidem : ∀ x, e (e x) = e x) (hmono : Monotone e) (S : Set (IdemFix e)) :
    letI := completeLattice hidem hmono
    ((sSup S : IdemFix e) : L) = e (sSup (Subtype.val '' S)) := rfl

theorem incl_preservesDirectedSup (hidem : ∀ x, e (e x) = e x) (hsc : PreservesDirectedSup e) :
    letI := completeLattice hidem (preservesDirectedSup_monotone hsc)
    PreservesDirectedSup (Subtype.val : IdemFix e → L) := by
  let := completeLattice hidem (preservesDirectedSup_monotone hsc)
  intro S hS hSdir
  show e (sSup (Subtype.val '' S)) = sSup (Subtype.val '' S)
  have hdir' : DirectedOn (· ≤ ·) (Subtype.val '' S) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hac, hbc⟩ := hSdir a ha b hb
    exact ⟨c.val, Set.mem_image_of_mem _ hc, hac, hbc⟩
  have hne' : (Subtype.val '' S).Nonempty := hS.image _
  rw [hsc hne' hdir']
  congr 1
  rw [← Set.image_comp]
  exact Set.image_congr (fun s _ => s.2)

theorem retr_preservesDirectedSup (hidem : ∀ x, e (e x) = e x) (hsc : PreservesDirectedSup e) :
    letI := completeLattice hidem (preservesDirectedSup_monotone hsc)
    PreservesDirectedSup (fun x : L => (⟨e x, hidem x⟩ : IdemFix e)) := by
  let := completeLattice hidem (preservesDirectedSup_monotone hsc)
  have hmono := preservesDirectedSup_monotone hsc
  intro T hT hTdir
  apply Subtype.ext
  rw [coe_sSup hidem hmono]
  show e (sSup T) = e (sSup (Subtype.val '' ((fun x : L => (⟨e x, hidem x⟩ : IdemFix e)) '' T)))
  have himg : Subtype.val '' ((fun x : L => (⟨e x, hidem x⟩ : IdemFix e)) '' T) = e '' T := by
    rw [← Set.image_comp]; rfl
  rw [himg]
  have hTdir' : DirectedOn (· ≤ ·) (e '' T) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hac, hbc⟩ := hTdir a ha b hb
    exact ⟨e c, Set.mem_image_of_mem _ hc, hmono hac, hmono hbc⟩
  have hTne' : (e '' T).Nonempty := hT.image _
  rw [hsc hT hTdir, hsc hTne' hTdir']
  congr 1
  rw [← Set.image_comp]
  exact Set.image_congr (fun x _ => (hidem x).symm)

noncomputable def retraction (hidem : ∀ x, e (e x) = e x) (hsc : PreservesDirectedSup e) :
    @IsContinuousLatticeRetraction (IdemFix e) L
      (completeLattice hidem (preservesDirectedSup_monotone hsc)) _ :=
  letI := completeLattice hidem (preservesDirectedSup_monotone hsc)
  { incl := ⟨Subtype.val,
      continuous_of_preservesDirectedSup (incl_preservesDirectedSup hidem hsc)⟩
    retr := ⟨fun x => ⟨e x, hidem x⟩,
      continuous_of_preservesDirectedSup (retr_preservesDirectedSup hidem hsc)⟩
    retr_incl := fun k => Subtype.ext k.2 }

theorem isContinuousLattice (hidem : ∀ x, e (e x) = e x) (hsc : PreservesDirectedSup e)
    (hL : ContinuousLattice L) :
    @ContinuousLattice (IdemFix e) (completeLattice hidem (preservesDirectedSup_monotone hsc)) := by
  let := completeLattice hidem (preservesDirectedSup_monotone hsc)
  exact proposition_2_10.a (retraction hidem hsc) hL

theorem scottTopology (hidem : ∀ x, e (e x) = e x) (hsc : PreservesDirectedSup e)
    (hL : ContinuousLattice L) :
    @scottTopologicalSpace (IdemFix e)
        (completeLattice hidem (preservesDirectedSup_monotone hsc)) =
      TopologicalSpace.induced (Subtype.val : IdemFix e → L) scottTopologicalSpace := by
  let := completeLattice hidem (preservesDirectedSup_monotone hsc)
  exact proposition_2_10.b (retraction hidem hsc) hL

end IdemFix

end DomainTheory.ContinuousLattice
