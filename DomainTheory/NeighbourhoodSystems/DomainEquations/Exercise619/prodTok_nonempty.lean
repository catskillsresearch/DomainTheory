module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example62 ExampleB

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


/-- The concrete product is again `∅`-free (every neighbourhood contains `Λ`). -/
theorem prodTok_nonempty : ∀ W, (prodTok D₀ D₁).mem W → W.Nonempty := by
  rintro W ⟨X, Y, _, _, rfl⟩; exact ⟨[], mem_prodTokNbhd_nil⟩

end Exercise619
end DomainTheory.NeighbourhoodSystems
