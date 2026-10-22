module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}


variable {hD : ∀ X, D.mem X → X.Nonempty}


variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}


/-- **`a§`, unfolded one step through the `U§ ⊴ U` projection pair.** Mirrors
`Proposition810.lean`'s `toElementMap_prodComb`/`toElementMap_arrowComb` pattern. -/
theorem toElementMap_aSharp (a : ApproximableMap U U) (x : U.Element) :
    (aSharp a).toElementMap x
      = iSharp.toElementMap ((aSharpInner a).toElementMap (jSharp.toElementMap x)) := by
  rw [aSharp_eq]
  simp only [toElementMap_comp]

end DomainTheory.NeighbourhoodSystems
