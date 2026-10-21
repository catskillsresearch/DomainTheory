/-ai
The minimum left endpoint of the canonical presenting list of an index is strictly less than the decoded midpoint.

Rewrite the decoded midpoint, then compare a left-hand summand with its average using the inequality of the minimum left endpoint and the maximum right endpoint.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMinFst
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2MidCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.decodeRat_splitU2MidCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2_min_lt_max

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem splitU2_min_lt_mid (n : ℕ) :
    listMinFst (decodeQPairList (canonCode n)) < decodeRat (splitU2MidCode n) := by
  rw [decodeRat_splitU2MidCode]; exact left_lt_add_div_two.mpr (splitU2_min_lt_max n)

end DomainTheory.NeighbourhoodSystems
