/-ai
Proposition 3.2(i) of Scott (1981, PRG-19) states that the pairing of x and y lies below the pairing of x' and y' if and only if x lies below x' and y lies below y'.

If the pairings are ordered, a neighbourhood of x padded by the second master belongs to the lower pairing and hence to the upper one, and injectivity of product neighbourhoods returns it to x'; the symmetric argument with the first master gives the inequality for y. Conversely, a product of neighbourhoods of x and y is a product of neighbourhoods of x' and y' by the two inequalities.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}










variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}














/-- **Proposition 3.2(i) (Scott 1981, PRG-19).** `⟨x, y⟩ ⊑ ⟨x', y'⟩ ↔ x ⊑ x' ∧ y ⊑ y'`. -/
theorem pair_le_pair_iff {x x' : V₀.Element} {y y' : V₁.Element} :
    pair x y ≤ pair x' y' ↔ x ≤ x' ∧ y ≤ y' := by
  constructor
  · intro h
    refine ⟨fun X hX => ?_, fun Y hY => ?_⟩
    · obtain ⟨X', Y', hX', hY', heq⟩ :=
        h (prodNbhd X V₁.master) ⟨X, V₁.master, hX, y.master_mem, rfl⟩
      obtain ⟨rfl, _⟩ := prodNbhd_injective heq
      exact hX'
    · obtain ⟨X', Y', hX', hY', heq⟩ :=
        h (prodNbhd V₀.master Y) ⟨V₀.master, Y, x.master_mem, hY, rfl⟩
      obtain ⟨_, rfl⟩ := prodNbhd_injective heq
      exact hY'
  · rintro ⟨hx, hy⟩ W ⟨X, Y, hX, hY, rfl⟩
    exact ⟨X, Y, hx X hX, hy Y hY, rfl⟩

end DomainTheory.NeighbourhoodSystems
