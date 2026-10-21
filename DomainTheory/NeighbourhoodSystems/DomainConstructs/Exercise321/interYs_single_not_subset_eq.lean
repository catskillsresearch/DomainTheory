/-ai
For a single step, if the input is not contained in the step input, the intersection of the relevant outputs is the codomain master.

A token lies in that intersection when it lies in the master and every listed step whose input contains the given input contributes its output. The only listed step fails that input condition, so the condition is membership in the master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- For a single step `[Y, Z]` and an input `X ⊄ Y`, the intersection is the whole master `Δ₂`. -/
theorem interYs_single_not_subset_eq {YX : Set α} {Z : Set β} {X : Set α}
    (hXY : ¬ X ⊆ YX) : interYs V₁.master [(YX, Z)] X = V₁.master := by
  ext z
  rw [mem_interYs]
  constructor
  · rintro ⟨hm, _⟩; exact hm
  · intro hz
    exact ⟨hz, fun p hp hXp => by rw [List.mem_singleton] at hp; subst hp; exact absurd hXp hXY⟩

end DomainTheory.NeighbourhoodSystems
