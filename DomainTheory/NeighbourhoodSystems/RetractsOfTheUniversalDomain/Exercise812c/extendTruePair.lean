/-ai
extendTruePair extends a finite sequence of Boolean pairs to a sequence on all natural numbers by padding each component separately, filling every index at or beyond the finite length with the true bit.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- Pad `δ' : Fin n → Bool × Bool` to a total `ℕ → Bool × Bool`, filling positions `≥ n` with
`(true, true)`. -/
def extendTruePair {n : ℕ} (δ' : Fin n → Bool × Bool) : ℕ → Bool × Bool :=
  fun i => (extendTrue (Prod.fst ∘ δ') i, extendTrue (Prod.snd ∘ δ') i)

end DomainTheory.NeighbourhoodSystems
