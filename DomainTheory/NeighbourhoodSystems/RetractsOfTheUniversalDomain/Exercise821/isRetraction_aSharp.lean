/-ai
If the inner sharp of an endomap of the universal domain is a retraction, then the sharp of that endomap is a retraction.

Compare the two maps on elements. Unfolding the sharp twice, cancelling the tree-algebra projection after the embedding, and using idempotence of the inner sharp shows that the sharp composed with itself agrees with the sharp.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.toElementMap_aSharp

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}



variable {hD : ∀ X, D.mem X → X.Nonempty}








variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}












/-- **Exercise 8.21(b)(3).** Idempotence of `aSharpInner a` transports through the projection pair
`iSharp`/`jSharp` to idempotence of `aSharp a` itself — exactly `Proposition810.lean`'s
`isRetraction_prodComb`/`isRetraction_arrowComb` recipe (`toElementMap_of_comp_eq_idMap` +
`toElementMap_idem_of_isRetraction`), conjugated through `jSharp_comp_iSharp` instead of
`jTimes_comp_iTimes`/`jArrow_comp_iArrow`. -/
theorem isRetraction_aSharp {a : ApproximableMap U U} (ha2 : IsRetraction (aSharpInner a)) :
    IsRetraction (aSharp a) := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, toElementMap_aSharp a ((aSharp a).toElementMap x),
    toElementMap_aSharp a x, toElementMap_of_comp_eq_idMap jSharp_comp_iSharp,
    toElementMap_idem_of_isRetraction ha2]

end DomainTheory.NeighbourhoodSystems
