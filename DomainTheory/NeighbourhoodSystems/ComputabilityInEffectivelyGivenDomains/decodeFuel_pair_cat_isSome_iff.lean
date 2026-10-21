/-ai
The option that forms the concatenation of the two fuel-bounded decodes of the subcodes of a code is defined if and only if both of those decodes are defined.

Case analysis on the two decodes; each combination simplifies.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

theorem decodeFuel_pair_cat_isSome_iff (fuel c : ℕ) :
    (match decodeFuel fuel c.unpair.2.unpair.1, decodeFuel fuel c.unpair.2.unpair.2 with
      | some a, some b => some (SExpr.cat a b) | _, _ => none).isSome = true ↔
      (decodeFuel fuel c.unpair.2.unpair.1).isSome = true ∧
        (decodeFuel fuel c.unpair.2.unpair.2).isSome = true := by
  cases decodeFuel fuel c.unpair.2.unpair.1 <;> cases decodeFuel fuel c.unpair.2.unpair.2 <;> simp

end Exercise722

end DomainTheory.NeighbourhoodSystems
