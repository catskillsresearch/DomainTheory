/-ai
If f is Scott continuous, then the greatest postfixed point below b is contained in the intersection of its image under f with b.

An element of the defining union lies in some admissible set. That set is contained in the greatest postfixed point, so monotonicity of f carries the membership in the image into the image of the greatest postfixed point, while the same membership already lies in b.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.gfpBelow

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem gfpBelow_postfixed {f : Pomega → Pomega} (hf : IsScottContinuous f)
    (b : Pomega) : gfpBelow f b ⊆ f (gfpBelow f b) ∩ b := by
  intro k hk
  obtain ⟨x, hx, hkx⟩ := Set.mem_sUnion.mp hk
  have hxz : x ⊆ gfpBelow f b := fun _ hm => Set.mem_sUnion.mpr ⟨x, hx, hm⟩
  exact ⟨isScottContinuous_monotone hf hxz (hx hkx).1, (hx hkx).2⟩

end DomainTheory.DataTypesAsLattices
