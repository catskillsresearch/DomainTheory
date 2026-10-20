module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- The low-bit AND `(x &&& y) % 2`, in arithmetic `{0,1}`-valued form: simply the product of the
low bits (`1` iff both are `1`). -/
def lowAnd (x y : ℕ) : ℕ := x % 2 * (y % 2)

end DomainTheory.NeighbourhoodSystems
