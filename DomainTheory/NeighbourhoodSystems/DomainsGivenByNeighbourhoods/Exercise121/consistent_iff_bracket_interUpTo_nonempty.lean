module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise121.IsComplete
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise121.filterFixedBy
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise121.bracket_nonempty_iff

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- **Exercise 1.21 — consistency via the intersection `[⋂]`.** For `X₀, …, Xₙ₋₁ ∈ 𝒟`,
`⟨Xᵢ⟩` is consistent iff `[⋂_{i<n} Xᵢ] ≠ ∅`. Combines Theorem 1.1c
(`consistent_iff_interUpTo_mem`) with `bracket_nonempty_iff`. -/
theorem consistent_iff_bracket_interUpTo_nonempty (X : ℕ → Set α) {n : ℕ}
    (hX : ∀ i, i < n → V.mem (X i)) :
    V.Consistent X n ↔ (V.bracket (V.interUpTo X n)).Nonempty := by
  rw [V.consistent_iff_interUpTo_mem X hX]
  exact V.bracket_nonempty_iff.symm

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
