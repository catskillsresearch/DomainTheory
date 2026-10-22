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
