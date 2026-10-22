module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

section DsharpFunctor

variable {γ δ ε : Type*} {D₀ : NeighborhoodSystem γ} {D₁ : NeighborhoodSystem δ}
  {D₂ : NeighborhoodSystem ε}

variable (hD₀ : ∀ X, D₀.mem X → X.Nonempty) (hD₁ : ∀ X, D₁.mem X → X.Nonempty)
  {hD₂ : ∀ X, D₂.mem X → X.Nonempty}

/-- **The action of `D ↦ D§` on morphisms.** Recurses `f : D₁ → D₀` through the leaves via `gMap`,
leaving the pairing structure alone — the general form of `aSharpInner` (which specializes this at
`D₀ = D₁ = U`, `f := a`). -/
noncomputable def dsharpMap (f : ApproximableMap D₁ D₀) :
    ApproximableMap (Dsharp D₁ hD₁) (Dsharp D₀ hD₀) :=
  gMap ((inSharpMap hD₀).comp f) (pairSharpMap hD₀) hD₁

end DsharpFunctor

end DomainTheory.NeighbourhoodSystems
