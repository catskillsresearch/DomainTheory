/-ai
The sharp of an endomap a of the universal domain is the conjugate of its inner recursive extension by the projection pair of the tree algebra of the universal domain into the universal domain: embed into the tree algebra, apply the inner extension, and project back.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.iSharp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.jSharp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.aSharpInner

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

/-- **Scott's operator `a§ : U → U`** (Exercise 8.21), conjugating `aSharpInner a` through the
`U§ ⊴ U` projection pair, exactly as Definition 8.9 builds `a+b`, `a×b`, `a→b`. -/
noncomputable def aSharp (a : ApproximableMap U U) : ApproximableMap U U :=
  iSharp.comp ((aSharpInner a).comp jSharp)

end DomainTheory.NeighbourhoodSystems
