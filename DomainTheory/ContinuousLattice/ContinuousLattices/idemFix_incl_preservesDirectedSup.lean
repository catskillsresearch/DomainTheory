module

public import DomainTheory.ContinuousLattice.ContinuousLattices.completeLattice
public import DomainTheory.ContinuousLattice.ScottMaps.preservesDirectedSup_monotone
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Topology Set

section FixedPoints

variable {L : Type*} [CompleteLattice L]

variable {e : L → L}

theorem idemFix_incl_preservesDirectedSup (hidem : ∀ x, e (e x) = e x)
    (hsc : PreservesDirectedSup e) :
    letI := IdemFix.completeLattice hidem (preservesDirectedSup_monotone hsc)
    PreservesDirectedSup (Subtype.val : IdemFix e → L) := by
  let := IdemFix.completeLattice hidem (preservesDirectedSup_monotone hsc)
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

end FixedPoints

end DomainTheory.ContinuousLattice
