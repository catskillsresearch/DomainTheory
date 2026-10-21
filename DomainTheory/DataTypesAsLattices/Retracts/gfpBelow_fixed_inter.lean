/-ai
If f is Scott continuous, then the intersection of the image of the greatest postfixed point below b with b equals that postfixed point.

One inclusion is the postfixed-point inequality. For the other, that inequality and monotonicity of f show that the intersection of the image with b is contained in the intersection of its own image with b, so the intersection belongs to the family whose union is the greatest postfixed point.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.gfpBelow
public import DomainTheory.DataTypesAsLattices.Retracts.gfpBelow_postfixed

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

theorem gfpBelow_fixed_inter {f : Pomega → Pomega} (hf : IsScottContinuous f)
    (b : Pomega) : f (gfpBelow f b) ∩ b = gfpBelow f b := by
  apply subset_antisymm
  · intro k hk
    refine Set.mem_sUnion.mpr ⟨f (gfpBelow f b) ∩ b, ?_, hk⟩
    have hle : gfpBelow f b ⊆ f (gfpBelow f b) ∩ b := gfpBelow_postfixed hf b
    have : f (gfpBelow f b) ⊆ f (f (gfpBelow f b) ∩ b) :=
      isScottContinuous_monotone hf hle
    intro m hm
    exact ⟨this hm.1, hm.2⟩
  · exact gfpBelow_postfixed hf b

end DomainTheory.DataTypesAsLattices
