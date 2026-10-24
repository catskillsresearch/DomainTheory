module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise_8_11

@[expose] public section

section
/- concordance: source L5147 EXERCISE 8.12 integer presentation of U -/
-- Exercise812/affine_2.lean
namespace DomainTheory.NeighbourhoodSystems
namespace affine

open NeighborhoodSystem


theorem eq_empty_of_ge {k ℓ : ℕ} (hℓ : 2 ^ k ≤ ℓ) : affine k ℓ = ∅ := by
  ext n
  simp only [mem_affine, Set.mem_empty_iff_false, iff_false]
  intro h
  have hlt : n % 2 ^ k < 2 ^ k := Nat.mod_lt n (by positivity)
  omega

end affine
end DomainTheory.NeighbourhoodSystems
end

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

end
end DomainTheory.NeighbourhoodSystems
end
