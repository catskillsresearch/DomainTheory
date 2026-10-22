module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.leftN

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem X_eq_master_of_embT_subset_leftN {B X : Set Str} (hB : B.Nonempty)
    (h : embBit true B ⊆ leftN D₀ D₁ X) : X = D₀.master := by
  obtain ⟨σ, hσ⟩ := hB
  rcases h ⟨σ, rfl, hσ⟩ with ⟨w', hw', -⟩ | ⟨-, hXm⟩
  · rw [List.cons.injEq] at hw'; exact absurd hw'.1 (by decide)
  · exact hXm

end Exercise627

end DomainTheory.NeighbourhoodSystems
