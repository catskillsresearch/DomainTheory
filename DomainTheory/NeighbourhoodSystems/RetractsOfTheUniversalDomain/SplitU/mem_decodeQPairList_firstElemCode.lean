/-ai
If a list code is nonzero, the rational pair decoded from its head code lies in the decoded list.

Write the code as a successor. The head code is the first component of the predecessor, and decoding the successor list puts the image of that head in the mapped list.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem


theorem mem_decodeQPairList_firstElemCode {c : ℕ} (hc : c ≠ 0) :
    decodeRatPair (firstElemCode c) ∈ decodeQPairList c := by
  obtain ⟨c', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hc
  have : firstElemCode (c' + 1) = c'.unpair.1 := by unfold firstElemCode; simp
  unfold decodeQPairList
  rw [this, decodeList_succ]
  exact List.mem_map_of_mem (by simp)

end DomainTheory.NeighbourhoodSystems
