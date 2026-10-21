/-ai
A fixed point of f that lies below every member of a family lies below the greatest postfixed point of f below the intersection of the family.

The fixed-point equation and those lower bounds place the element in the intersection of its image with the intersection of the family, so it belongs to the family of sets whose union is that greatest postfixed point.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Fixpoints
public import DomainTheory.DataTypesAsLattices.Retracts.gfpBelow

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem gfpBelow_isGLB {f : Pomega → Pomega} (_hf : IsScottContinuous f)
    {A : Set Pomega} (_hA : A ⊆ Fixpoints f) {z : Pomega}
    (hz : f z = z) (hlb : ∀ x ∈ A, z ⊆ x) :
    z ⊆ gfpBelow f (⋂₀ A) := by
  have hzI : z ⊆ ⋂₀ A := fun k hk y hy => hlb y hy hk
  have hpost : z ⊆ f z ∩ ⋂₀ A := fun k hk => ⟨by rwa [hz], hzI hk⟩
  exact fun k hk => Set.mem_sUnion.mpr ⟨z, hpost, hk⟩

end DomainTheory.DataTypesAsLattices
