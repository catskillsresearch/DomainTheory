/-ai
restrictFinPair cuts a sequence of Boolean pairs down to the finite initial segment of a given length, reading the sequence at the underlying index of each finite position.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- Restrict `δ : ℕ → Bool × Bool` to `Fin n → Bool × Bool`. -/
def restrictFinPair (δ : ℕ → Bool × Bool) (n : ℕ) : Fin n → Bool × Bool := fun i => δ i.val

end DomainTheory.NeighbourhoodSystems
