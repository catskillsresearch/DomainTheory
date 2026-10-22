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

theorem leftN_master : leftN D₀ D₁ D₀.master = sumTokMaster D₀ D₁ := by
  apply Set.eq_of_subset_of_subset
  · rintro w (hw | ⟨hw, -⟩)
    · exact embF_subset_sumTokMaster D₀.master_mem hw
    · exact hw
  · exact fun w hw => Or.inr ⟨hw, rfl⟩

end Exercise627

end DomainTheory.NeighbourhoodSystems
