/-ai
Decoding the concatenation of two list codes yields the concatenation of the two decoded lists of quoted pairs.

Unfold the decoder and rewrite by the equation for appending list codes and by preservation of concatenation under mapping.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- `decodeQPairList` commutes with `appendListCode` (it is just `decodeList` followed by a fixed
`map`, and `List.map` commutes with `++`). -/
theorem decodeQPairList_appendListCode (c1 c2 : ℕ) :
    decodeQPairList (appendListCode c1 c2) = decodeQPairList c1 ++ decodeQPairList c2 := by
  unfold decodeQPairList
  rw [appendListCode_eq, List.map_append]

end DomainTheory.NeighbourhoodSystems
