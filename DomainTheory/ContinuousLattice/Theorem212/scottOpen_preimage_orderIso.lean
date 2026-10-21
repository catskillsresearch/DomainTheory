/-ai
The preimage of a Scott-open set under an order isomorphism is Scott-open.

The preimage is an upper set because the isomorphism is monotone and the original set is an upper set. If a nonempty directed set has supremum in the preimage, its image is nonempty and directed, and the isomorphism preserves suprema, so the image of the supremum is the supremum of the image and lies in the original set. Scott-openness supplies a point of the image already in the set, and that point is the image of a member of the original set.
ai-/
module

public import DomainTheory.ContinuousLattice.Constructions
public import DomainTheory.ContinuousLattice.FunctionSpaces

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.ContinuousLattice

open Topology Set

universe u

section Theorem212Transfer

variable {A B : Type u} [latticeA : CompleteLattice A] [latticeB : CompleteLattice B]

/-- An order isomorphism pulls Scott-open sets back to Scott-open sets. -/
theorem scottOpen_preimage_orderIso (e : A ≃o B) {U : Set B} (hU : ScottOpen U) :
    ScottOpen (e ⁻¹' U) := by
  refine ⟨fun x y hxy hx => hU.1 (e.monotone hxy) hx, ?_⟩
  intro S hSne hSdir hsup
  have hImgNe : (e '' S).Nonempty := hSne.image e
  have hImgDir : DirectedOn (· ≤ ·) (e '' S) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hxz, hyz⟩ := hSdir x hx y hy
    exact ⟨e z, Set.mem_image_of_mem e hz, e.monotone hxz, e.monotone hyz⟩
  have hmap : e (sSup S) = sSup (e '' S) := by
    rw [e.map_sSup, sSup_image]
  obtain ⟨_, ⟨s, hs, rfl⟩, hes⟩ := hU.2 hImgNe hImgDir (hmap ▸ hsup)
  exact ⟨s, hs, hes⟩

end Theorem212Transfer

end DomainTheory.ContinuousLattice
