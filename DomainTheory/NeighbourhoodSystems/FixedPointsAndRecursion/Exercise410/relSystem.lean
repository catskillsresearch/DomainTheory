/-ai
The relativized neighbourhood system below an element a has the same tokens and the same master neighbourhood as the original system, and its neighbourhoods are exactly the members of the filter a. The master belongs to a, every neighbourhood is contained in the master because it is a neighbourhood of the original system, and a is closed under consistent intersection.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- **Exercise 4.10 (Scott 1981, PRG-19).** The relativized neighbourhood system `Dₐ`: same tokens
and master, neighbourhoods exactly the members of the filter `a`. -/
def relSystem (a : V.Element) : NeighborhoodSystem α where
  mem X := a.mem X
  master := V.master
  master_nonempty := V.master_nonempty
  master_mem := a.master_mem
  sub_master := fun hX => V.sub_master (a.sub hX)
  inter_mem := fun hX hY _ _ => a.inter_mem hX hY

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
