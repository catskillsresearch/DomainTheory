module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

/-- The left-copy generator: `0X` for proper `X`, the shared bottom `sumTokMaster` for `X = Δ₀`. The
set-builder `{w ∣ w ∈ sumTokMaster ∧ X = Δ₀}` keeps the *definition* choice-free. -/
def leftN (D₀ D₁ : NeighborhoodSystem Str) (X : Set Str) : Set Str :=
  embBit false X ∪ {w | w ∈ sumTokMaster D₀ D₁ ∧ X = D₀.master}

end Exercise627

end DomainTheory.NeighbourhoodSystems
