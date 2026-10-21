/-ai
The union of a family of fixed points of a Scott-continuous map is contained in the image of that union.

An element of the union lies in some member. That member equals its image, so the element lies in the image of the member, and monotonicity along the inclusion of the member in the union puts the element in the image of the union.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Fixpoints

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

theorem sUnion_Fixpoints_le_image {f : Pomega → Pomega} (hf : IsScottContinuous f)
    {A : Set Pomega} (hA : A ⊆ Fixpoints f) :
    ⋃₀ A ⊆ f (⋃₀ A) := by
  intro k hk
  obtain ⟨x, hxA, hkx⟩ := Set.mem_sUnion.mp hk
  have hx : f x = x := hA hxA
  have : k ∈ f x := by rwa [hx]
  exact isScottContinuous_monotone hf (Set.subset_sUnion_of_mem hxA) this

end DomainTheory.DataTypesAsLattices
