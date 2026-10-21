/-ai
The unary sequence system on the naturals is the nested-or-disjoint neighbourhood system whose neighbourhoods are the tails and the singletons, whose master is the set of all naturals, and in which every neighbourhood is contained in that master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.mem_tail
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.memC1
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.memC1_univ
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.nestedOrDisjoint

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise425

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

/-- **Exercise 4.25 (Scott 1981, PRG-19).** The unary sequence system `C₁` on `Δ = {1}* ≅ ℕ`. -/
def C1 : NeighborhoodSystem ℕ :=
  NeighborhoodSystem.ofNestedOrDisjoint memC1 Set.univ Set.univ_nonempty
    memC1_univ nestedOrDisjoint
    (fun _ => Set.subset_univ _)

end DomainTheory.NeighbourhoodSystems.Exercise425
