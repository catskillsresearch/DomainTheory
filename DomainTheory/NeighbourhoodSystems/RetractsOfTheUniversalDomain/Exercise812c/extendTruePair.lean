module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.IsEffectivelyGiven
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- Pad `δ' : Fin n → Bool × Bool` to a total `ℕ → Bool × Bool`, filling positions `≥ n` with
`(true, true)`. -/
def extendTruePair {n : ℕ} (δ' : Fin n → Bool × Bool) : ℕ → Bool × Bool :=
  fun i => (extendTrue (Prod.fst ∘ δ') i, extendTrue (Prod.snd ∘ δ') i)

end DomainTheory.NeighbourhoodSystems
