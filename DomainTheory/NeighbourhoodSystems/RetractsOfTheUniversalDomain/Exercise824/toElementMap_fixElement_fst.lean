/-ai
Applying the first of the two maps to the fixed element of their pairing recovers the first component of that fixed element.

The paired map fixes its fixed element. Rewrite that equation by the element action of the pairing, apply the first projection, and rewrite by the first projection of a pair.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Sub8_6 Exercise823

namespace Exercise824

variable {α : Type} {E : NeighborhoodSystem α}













theorem toElementMap_fixElement_fst (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) :
    s.toElementMap (paired s t).fixElement = (paired s t).fixElement.fst := by
  have h : (paired s t).toElementMap (paired s t).fixElement = (paired s t).fixElement :=
    toElementMap_fixElement (paired s t)
  rw [toElementMap_paired] at h
  have h' := congrArg NeighborhoodSystem.Element.fst h
  rwa [fst_pair] at h'

end Exercise824
end DomainTheory.NeighbourhoodSystems
