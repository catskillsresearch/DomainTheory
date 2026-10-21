/-ai
The curry step code of a number a and a code e is one more than the pair whose first component pairs the pair of a with the first component of e and the second component of e, and whose second component is zero. It is the code of the one-entry function-space neighbourhood consisting of the step from the product of the neighbourhoods coded by a and by the first component of e to the neighbourhood coded by the second component.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}

/-- The code of the one-entry function-space neighbourhood `[⟨X_{e.1}, X_{e'.1}⟩, X_{e'.2}]` of
`(𝒟₀×𝒟₁→𝒟₂)` (a `Xenum`-singleton over the product presentation). -/
def curryStepCode (a e' : ℕ) : ℕ :=
  Nat.pair (Nat.pair (Nat.pair a e'.unpair.1) e'.unpair.2) 0 + 1

end DomainTheory.NeighbourhoodSystems
