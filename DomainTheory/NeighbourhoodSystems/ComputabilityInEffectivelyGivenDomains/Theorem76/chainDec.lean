/-ai
The decidable chain predicate, relative to an inclusion characteristic and a function-space code, holds of any start index on the empty list. On a cons it holds when the characteristic accepts the function-space code paired with the one-entry code of the current index and the head, and the predicate holds of the head on the tail.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.codePair

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

variable (P : ComputablePresentation V)

/-- The decidable mirror of `gStepsOK`, phrased with the function-space inclusion char `fincl`. -/
def chainDec (fincl : ℕ → ℕ) (c : ℕ) : ℕ → List ℕ → Prop
  | _, [] => True
  | a, (b :: rest) => fincl (Nat.pair c (codePair a b)) = 1 ∧ chainDec fincl c b rest

end DomainTheory.NeighbourhoodSystems
