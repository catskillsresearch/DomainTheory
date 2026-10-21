/-ai
Applying the inverse sum map after the forward sum map returns the original element of the concrete token sum.

Two elements agree when they contain the same neighbourhoods. A neighbourhood of the round trip is the master, which every element contains, or a false-tagged copy, which the left-injection criterion returns to the original element, or a true-tagged copy, which the right-injection criterion returns. Conversely, the subset law says a neighbourhood of the original element is the master, a false-tagged copy, or a true-tagged copy, and each case is the matching clause of the inverse image, using the reverse directions of those two criteria.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sumTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.toSum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.toSum_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.toSum_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.fromSum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.fromSum_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.fromSum_mem_embT

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example62 ExampleB

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem fromSum_toSum (x : (sumTok D₀ D₁ h₀ h₁).Element) : fromSum (toSum x) = x := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, hX, rfl, hs⟩ | ⟨Y, hY, rfl, hs⟩)
    · exact x.master_mem
    · exact (toSum_mem_inj₀ hX).mp hs
    · exact (toSum_mem_inj₁ hY).mp hs
  · intro hW
    rcases x.sub hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, hX, rfl, (toSum_mem_inj₀ hX).mpr hW⟩)
    · exact Or.inr (Or.inr ⟨Y, hY, rfl, (toSum_mem_inj₁ hY).mpr hW⟩)

end Exercise619

end DomainTheory.NeighbourhoodSystems
