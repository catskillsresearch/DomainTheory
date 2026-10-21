/-ai
If two indices present the same neighbourhood of U, their midpoint codes decode to the same rational. The midpoint used by the left and right splits depends only on the presented set.

The common neighbourhood means the two canonical presenting lists present the same intervals. The minimum left endpoint and the maximum right endpoint of those nonempty lists of nondegenerate bounded pairs therefore agree. Rewriting both decoded midpoints by the midpoint formula substitutes those two equalities.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.forall_bounds_decodeQPairList_canonCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMinFst_congr
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMaxSnd_congr
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2MidCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.decodeRat_splitU2MidCode

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`splitU2Left`/`splitU2Right`'s midpoint depends only on `UX n` as a set** — the key lemma
that `SplitU.lean`'s `splitULeft`/`splitURight` lack, via `listMinFst_congr`/`listMaxSnd_congr`. -/
theorem splitU2MidCode_congr {n n' : ℕ} (h : UX n = UX n') :
    decodeRat (splitU2MidCode n) = decodeRat (splitU2MidCode n') := by
  have heqP : presentedIntervals (decodeQPairList (canonCode n))
      = presentedIntervals (decodeQPairList (canonCode n')) := h
  have hminEq := listMinFst_congr (decodeQPairList_canonCode_ne_nil n)
    (decodeQPairList_canonCode_ne_nil n') (forall_lt_decodeQPairList_canonCode n)
    (forall_bounds_decodeQPairList_canonCode n) (forall_lt_decodeQPairList_canonCode n')
    (forall_bounds_decodeQPairList_canonCode n') heqP
  have hmaxEq := listMaxSnd_congr (decodeQPairList_canonCode_ne_nil n)
    (decodeQPairList_canonCode_ne_nil n') (forall_lt_decodeQPairList_canonCode n)
    (forall_bounds_decodeQPairList_canonCode n) (forall_lt_decodeQPairList_canonCode n')
    (forall_bounds_decodeQPairList_canonCode n') heqP
  rw [decodeRat_splitU2MidCode, decodeRat_splitU2MidCode, hminEq, hmaxEq]

end DomainTheory.NeighbourhoodSystems
