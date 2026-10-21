/-ai
The inclusion of the fixed-point set into the ambient lattice preserves directed suprema.

The underlying element of a directed supremum of fixed points is the endomap applied to the supremum of the underlying set. The image of a nonempty directed set of fixed points is nonempty, and it is directed because a common upper bound among the fixed points remains a common upper bound after the subtype is forgotten. Preservation of directed suprema by the endomap rewrites the left side as the supremum of the image of that underlying set under the endomap. On fixed points the endomap is the identity, so that image is the underlying set.
ai-/
module

public import DomainTheory.ContinuousLattice.Constructions
public import DomainTheory.ContinuousLattice.FunctionSpaces
public import DomainTheory.ContinuousLattice.Theorem212.IdemFix
public import DomainTheory.ContinuousLattice.Theorem212.completeLattice

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
