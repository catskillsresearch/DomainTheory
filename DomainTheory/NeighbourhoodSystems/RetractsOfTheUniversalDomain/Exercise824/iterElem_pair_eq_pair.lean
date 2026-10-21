/-ai
The n-th approximant of the paired map is the pairing of the filters of the n-th approximants of the two component operators.

Unfold the component operators as the approximable maps of the two components of the iterate. The round trip from an element through its approximable map and back to its filter, on both components, together with pairing those two components, gives the identity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Sub8_6 Exercise823

namespace Exercise824

variable {α : Type} {E : NeighborhoodSystem α}











/-- The `n`-th approximant of `⟨s, t⟩` is exactly the pairing of `aOp`'s and `bOp`'s `n`-th
approximants (`Product.lean`'s `pair_fst_snd`, transported through the `toFilter`/`toApproxMap`
round trip). -/
theorem iterElem_pair_eq_pair (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) (n : ℕ) :
    (paired s t).iterElem n = pair (toFilter (aOp s t n)) (toFilter (bOp s t n)) := by
  show (paired s t).iterElem n
      = pair (toFilter (toApproxMap ((paired s t).iterElem n).fst))
          (toFilter (toApproxMap ((paired s t).iterElem n).snd))
  rw [toFilter_toApproxMap, toFilter_toApproxMap, pair_fst_snd]

end Exercise824
end DomainTheory.NeighbourhoodSystems
