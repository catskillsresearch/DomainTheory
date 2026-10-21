/-ai
Applying the second of the two maps to the fixed element of their pairing recovers the second component of that fixed element.

The paired map fixes its fixed element. Rewrite that equation by the element action of the pairing, apply the second projection, and rewrite by the second projection of a pair.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Sub8_6 Exercise823

namespace Exercise824

variable {α : Type} {E : NeighborhoodSystem α}













theorem toElementMap_fixElement_snd (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) :
    t.toElementMap (paired s t).fixElement = (paired s t).fixElement.snd := by
  have h : (paired s t).toElementMap (paired s t).fixElement = (paired s t).fixElement :=
    toElementMap_fixElement (paired s t)
  rw [toElementMap_paired] at h
  have h' := congrArg NeighborhoodSystem.Element.snd h
  rwa [snd_pair] at h'

end Exercise824
end DomainTheory.NeighbourhoodSystems
