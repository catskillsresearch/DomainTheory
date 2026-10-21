/-ai
Decoding the boolean-list code of a list of booleans recovers that list.

Unfold both sides. List decoding inverts list encoding, and the boolean interpretation passes inside the list map. Induction on the list: the empty list is immediate, and a cons cell is checked by cases on the head boolean, using the boolean encoding, the natural-to-boolean interpretation, and the inductive hypothesis.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.boolNat
import all DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.natBool
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.encodeListBool
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeListBool

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

theorem decodeListBool_encodeListBool (σ : List Bool) :
    decodeListBool (encodeListBool σ) = some σ := by
  simp [decodeListBool, encodeListBool, decodeList_encodeList, List.mapM_map]
  induction σ with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> simp [boolNat, natBool, ih]

end Exercise722

end DomainTheory.NeighbourhoodSystems
