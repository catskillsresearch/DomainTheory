module

public import DomainTheory.ContinuousLattice.ContinuousLattices.IdempotentFixedPoint.completeLattice
public import DomainTheory.ContinuousLattice.FunctionSpaces.IsContinuousLatticeRetraction
public import DomainTheory.ContinuousLattice.FunctionSpaces.proposition_2_10
public import DomainTheory.ContinuousLattice.ScottMaps.preservesDirectedSup_monotone
public import DomainTheory.ContinuousLattice.Specialization.scottTopologicalSpace
public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Topology Set

variable {L : Type*} [CompleteLattice L] {e : L → L}

namespace IdempotentFixedPoint

theorem incl_preservesDirectedSup (hidem : ∀ x, e (e x) = e x) (hsc : PreservesDirectedSup e) :
    letI := IdempotentFixedPoint.completeLattice hidem (preservesDirectedSup_monotone hsc)
    PreservesDirectedSup (Subtype.val : IdempotentFixedPoint e → L) := by
  let := IdempotentFixedPoint.completeLattice hidem (preservesDirectedSup_monotone hsc)
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
    letI := IdempotentFixedPoint.completeLattice hidem (preservesDirectedSup_monotone hsc)
    PreservesDirectedSup (fun x : L => (⟨e x, hidem x⟩ : IdempotentFixedPoint e)) := by
  let := IdempotentFixedPoint.completeLattice hidem (preservesDirectedSup_monotone hsc)
  have hmono := preservesDirectedSup_monotone hsc
  intro T hT hTdir
  apply Subtype.ext
  rw [completeLattice.coe hidem hmono]
  show e (sSup T) = e (sSup (Subtype.val '' ((fun x : L =>
      (⟨e x, hidem x⟩ : IdempotentFixedPoint e)) '' T)))
  have himg : Subtype.val '' ((fun x : L => (⟨e x, hidem x⟩ : IdempotentFixedPoint e)) '' T) =
      e '' T := by
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
    @IsContinuousLatticeRetraction (IdempotentFixedPoint e) L
      (IdempotentFixedPoint.completeLattice hidem (preservesDirectedSup_monotone hsc)) _ :=
  letI := IdempotentFixedPoint.completeLattice hidem (preservesDirectedSup_monotone hsc)
  { incl := ⟨Subtype.val,
      PreservesDirectedSup.continuous_of (incl_preservesDirectedSup hidem hsc)⟩
    retr := ⟨fun x => ⟨e x, hidem x⟩,
      PreservesDirectedSup.continuous_of (retr_preservesDirectedSup hidem hsc)⟩
    retr_incl := fun k => Subtype.ext k.2 }

theorem isContinuousLattice (hidem : ∀ x, e (e x) = e x) (hsc : PreservesDirectedSup e)
    (hL : ContinuousLattice L) :
    @ContinuousLattice (IdempotentFixedPoint e)
      (IdempotentFixedPoint.completeLattice hidem (preservesDirectedSup_monotone hsc)) := by
  let := IdempotentFixedPoint.completeLattice hidem (preservesDirectedSup_monotone hsc)
  exact proposition_2_10.a (retraction hidem hsc) hL

theorem scottTopology (hidem : ∀ x, e (e x) = e x) (hsc : PreservesDirectedSup e)
    (hL : ContinuousLattice L) :
    @scottTopologicalSpace (IdempotentFixedPoint e)
        (IdempotentFixedPoint.completeLattice hidem (preservesDirectedSup_monotone hsc)) =
      TopologicalSpace.induced (Subtype.val : IdempotentFixedPoint e → L) scottTopologicalSpace := by
  let := IdempotentFixedPoint.completeLattice hidem (preservesDirectedSup_monotone hsc)
  exact proposition_2_10.b (retraction hidem hsc) hL

end IdempotentFixedPoint

end DomainTheory.ContinuousLattice
