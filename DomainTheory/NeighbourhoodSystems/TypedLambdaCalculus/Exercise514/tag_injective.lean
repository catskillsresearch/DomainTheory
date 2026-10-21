/-ai
The tag is injective in the list and the output jointly: equal tags give equal lists and equal outputs.

The argument is induction on the first list. If both lists are empty, injectivity of the pairing equates the outputs. If one list is empty and the other is not, injectivity of the pairing forces a first coordinate 0 to equal a positive integer, which arithmetic rules out. If both lists are nonempty, injectivity of the pairing equates the incremented heads and the tags of the tails. Arithmetic equates the heads, and the inductive hypothesis equates the tails and the outputs.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise513
public import Mathlib.Data.List.Basic
import all Mathlib.Data.List.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise514

open DomainTheory.NeighbourhoodSystems.Exercise513


/-- **The tag is one-one**, jointly in both arguments (induction on the list + `num_injective`). -/
theorem tag_injective : ∀ {ns₁ ns₂ : List ℕ} {m₁ m₂ : ℕ},
    tag ns₁ m₁ = tag ns₂ m₂ → ns₁ = ns₂ ∧ m₁ = m₂ := by
  intro ns₁
  induction ns₁ with
  | nil =>
      intro ns₂ m₁ m₂ h
      cases ns₂ with
      | nil =>
          have hp := num_injective (show numP (0, m₁) = numP (0, m₂) from h)
          injection hp with _ hm
          exact ⟨rfl, hm⟩
      | cons n₂ ns₂' =>
          exfalso
          have hp := num_injective (show numP (0, m₁) = numP (n₂ + 1, tag ns₂' m₂) from h)
          injection hp with h1 _
          omega
  | cons n₁ ns₁' ih =>
      intro ns₂ m₁ m₂ h
      cases ns₂ with
      | nil =>
          exfalso
          have hp := num_injective (show numP (n₁ + 1, tag ns₁' m₁) = numP (0, m₂) from h)
          injection hp with h1 _
          omega
      | cons n₂ ns₂' =>
          have hp := num_injective
            (show numP (n₁ + 1, tag ns₁' m₁) = numP (n₂ + 1, tag ns₂' m₂) from h)
          injection hp with h1 h2
          have hn : n₁ = n₂ := by omega
          obtain ⟨hns, hm⟩ := ih h2
          exact ⟨by rw [hn, hns], hm⟩

end DomainTheory.NeighbourhoodSystems.Exercise514
