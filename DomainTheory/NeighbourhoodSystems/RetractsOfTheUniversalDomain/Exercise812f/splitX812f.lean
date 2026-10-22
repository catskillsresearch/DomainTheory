module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.U_noMinimal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.VDiff

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`splitX812f`: the exercise's literal target split**, `V` as prober against `U`'s canonical
bisection (`UBisection2`). -/
noncomputable def splitX812f : Set ℕ → Set ℚ → Set ℕ → Set ℚ × Set ℚ :=
  ComputableBisection.splitFromBisection VComputablePresentation V_isComputableDiff UBisection2
    U_noMinimal

end DomainTheory.NeighbourhoodSystems
