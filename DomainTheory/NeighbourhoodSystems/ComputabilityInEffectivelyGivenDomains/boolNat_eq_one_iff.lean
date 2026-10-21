/-ai
The boolean numeral of a boolean equals 1 if and only if the boolean is true.

Split into the two boolean cases and simplify the definition.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.boolNat

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

theorem boolNat_eq_one_iff (b : Bool) : boolNat b = 1 ↔ b := by
  cases b <;> simp [boolNat]

end Exercise722

end DomainTheory.NeighbourhoodSystems
