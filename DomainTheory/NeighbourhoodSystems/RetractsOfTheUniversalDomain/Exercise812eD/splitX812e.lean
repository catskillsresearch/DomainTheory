/-ai
The split of Exercise 8.12(e) sends a rational set, a set of natural numbers, and a rational set to a pair of sets of natural numbers by running the bisection split with U as prober against V's canonical bisection.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812eD.U_isComputableDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812eD.B812e

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`splitX812e`: the exercise's literal target split**, `U` as prober against `V`'s canonical
bisection. -/
noncomputable def splitX812e : Set ℚ → Set ℕ → Set ℚ → Set ℕ × Set ℕ :=
  ComputableBisection.splitFromBisection UComputablePresentation U_isComputableDiff B812e
    V_noMinimal

end DomainTheory.NeighbourhoodSystems
