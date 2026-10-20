module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.leftN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.embF_subset_leftN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.subset_of_embF_subset_leftN

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem leftN_subset_iff {X X' : Set Str} (hX : D₀.mem X) (hX' : D₀.mem X') :
    leftN D₀ D₁ X ⊆ leftN D₀ D₁ X' ↔ X ⊆ X' := by
  constructor
  · intro h
    exact subset_of_embF_subset_leftN (D₀.sub_master hX) (embF_subset_leftN.trans h)
  · intro hXX'
    rintro w (⟨w', rfl, hw'⟩ | ⟨hw, hXm⟩)
    · exact embF_subset_leftN ⟨w', rfl, hXX' hw'⟩
    · exact Or.inr ⟨hw, Set.Subset.antisymm (D₀.sub_master hX') (hXm ▸ hXX')⟩

end Exercise627

end DomainTheory.NeighbourhoodSystems
