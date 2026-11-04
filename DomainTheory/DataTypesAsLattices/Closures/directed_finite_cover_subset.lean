module

public import DomainTheory.DataTypesAsLattices.Retracts.DirectedSubset
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem directed_finite_cover_subset {f : Pomega → Pomega}
    {A : Set (Fixpoints f)} (hA : DirectedSubset A) {t : Pomega}
    (ht : t.Finite) (hsub : t ⊆ ⋃₀ (Subtype.val '' A)) :
    ∃ z ∈ A, t ⊆ z := by
  have hA' : DirectedSet A := by
    refine ⟨⟨hA.out.1, ?_⟩⟩
    intro x hx y hy
    obtain ⟨z, hz, hxz, hyz⟩ := hA.out.2 hx hy
    exact ⟨z, hz, hxz, hyz⟩
  simpa [Fixpoints.vals] using directed_finite_cover hA' ht (by
    simpa [Fixpoints.vals] using hsub)

end DomainTheory.DataTypesAsLattices
