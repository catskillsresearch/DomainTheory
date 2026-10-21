/-ai
Every neighbourhood of the abstract separated sum is nonempty.

The master contains the untagged token. A left injection of a nonempty neighbourhood is nonempty, and a right injection of a nonempty neighbourhood is nonempty.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example62 ExampleB

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem sum_mem_nonempty {W : Set (Option (Str ⊕ Str))} (h : (sum D₀ D₁ h₀ h₁).mem W) :
    W.Nonempty := by
  rcases h with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
  · exact ⟨none, none_mem_sumMaster⟩
  · exact inj₀_nonempty (h₀ X hX)
  · exact inj₁_nonempty (h₁ Y hY)

end Exercise619

end DomainTheory.NeighbourhoodSystems
