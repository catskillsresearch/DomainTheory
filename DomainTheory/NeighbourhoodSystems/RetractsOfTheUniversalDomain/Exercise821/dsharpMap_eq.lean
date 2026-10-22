module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.dsharpMap

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

theorem dsharpMap_eq (f : ApproximableMap D₁ D₀) :
    dsharpMap hD₀ hD₁ f = gMap ((inSharpMap hD₀).comp f) (pairSharpMap hD₀) hD₁ := rfl

end DsharpFunctor

end DomainTheory.NeighbourhoodSystems
