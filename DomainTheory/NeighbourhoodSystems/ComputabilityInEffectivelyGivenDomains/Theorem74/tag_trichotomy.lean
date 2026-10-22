module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.prodEnum_apply
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.prodPresentation_X

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- Choice-free three-way split of a tag `n ∈ {0, 1, ≥2}` (via `Nat.decEq`, not classical `em`). -/
theorem tag_trichotomy (n : ℕ) : n = 0 ∨ n = 1 ∨ (n ≠ 0 ∧ n ≠ 1) := by
  have h_dec : (n ≠ 0) ∨ (n = 0) := by
    by_cases h : n = 0
    · exact Or.inr h
    · exact Or.inl h
  rcases h_dec with h | h
  · have h'_dec : (n ≠ 1) ∨ (n = 1) := by
      by_cases h' : n = 1
      · exact Or.inr h'
      · exact Or.inl h'
    rcases h'_dec with h' | h'
    · exact Or.inr (Or.inr ⟨h, h'⟩)
    · exact Or.inr (Or.inl h')
  · exact Or.inl h

end DomainTheory.NeighbourhoodSystems
