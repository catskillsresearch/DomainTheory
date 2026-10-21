/-ai
The successor first approximant is the first operator applied to the previous first and second approximants.

Unfold both sides. The successor iterate of the paired operator is that operator applied to the previous iterate, its first component is the action of the first map, and the previous iterate is the pair of the filters of the two approximants.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.iterElem_succ_pair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.iterElem_pair_eq_pair

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Sub8_6 Exercise823

namespace Exercise824

variable {α : Type} {E : NeighborhoodSystem α}











/-- **The mutual recursion on approximants**: `aOp s t (n+1) = binOp s (aOp s t n) (bOp s t n)`. -/
theorem aOp_succ (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) (n : ℕ) :
    aOp s t (n + 1) = binOp s (aOp s t n) (bOp s t n) := by
  show toApproxMap ((paired s t).iterElem (n + 1)).fst
      = toApproxMap (s.toElementMap (pair (toFilter (aOp s t n)) (toFilter (bOp s t n))))
  rw [iterElem_succ_pair, toElementMap_paired, fst_pair, iterElem_pair_eq_pair]

end Exercise824
end DomainTheory.NeighbourhoodSystems
