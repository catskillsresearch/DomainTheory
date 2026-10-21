/-ai
A neighbourhood system is difference-closed when the set difference of any two of its neighbourhoods is empty or again a neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.IsEffectivelyGiven
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- **Difference-closure**, generalizing `U_diff_mem`/`V_diff_mem`: the set-difference of two
neighbourhoods is again a neighbourhood, or empty. -/
def NeighborhoodSystem.DiffClosed {α : Type*} (D : NeighborhoodSystem α) : Prop :=
  ∀ {X Y : Set α}, D.mem X → D.mem Y → X \ Y = ∅ ∨ D.mem (X \ Y)

end DomainTheory.NeighbourhoodSystems
