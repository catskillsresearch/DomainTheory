module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.gfpBelow

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem gfpBelow_subset (f : Pomega → Pomega) (b : Pomega) :
    gfpBelow f b ⊆ b := by
  intro k hk
  obtain ⟨x, hx, hkx⟩ := Set.mem_sUnion.mp hk
  exact (hx hkx).2

end DomainTheory.DataTypesAsLattices
