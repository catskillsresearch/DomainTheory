/-ai
The inner sharp of an endomap a of the universal domain is the catamorphism on its tree algebra that applies a on leaves and the tree algebra's own pairing on nodes.
ai-/
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

/-- **The "inner" recursive extension of `a : U → U` to `U§ → U§`**, satisfying `a§(x§) = (a x)§`
and `a§(⟨y,z⟩) = ⟨a§(y), a§(z)⟩` by `gMap_in`/`gMap_pair` — Scott's fixed-point construction for
`a§`, realized directly by Exercise 7.17 Part 2's catamorphism `gMap`. -/
noncomputable def aSharpInner (a : ApproximableMap U U) :
    ApproximableMap (Dsharp U U_mem_nonempty) (Dsharp U U_mem_nonempty) :=
  gMap ((inSharpMap U_mem_nonempty).comp a) (pairSharpMap U_mem_nonempty) U_mem_nonempty

end DomainTheory.NeighbourhoodSystems
