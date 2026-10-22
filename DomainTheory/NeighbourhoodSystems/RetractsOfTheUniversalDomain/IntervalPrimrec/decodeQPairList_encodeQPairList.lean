module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.decodeRatPair_encodeRatPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.encodeQPairList
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.decodeQPairList

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

@[simp] theorem decodeQPairList_encodeQPairList (L : List (ℚ × ℚ)) :
    decodeQPairList (encodeQPairList L) = L := by
  unfold decodeQPairList encodeQPairList
  rw [decodeList_encodeList, List.map_map]
  simp only [Function.comp_def, decodeRatPair_encodeRatPair, List.map_id_fun', id]

end DomainTheory.NeighbourhoodSystems
