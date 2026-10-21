/-ai
Division of a natural number m by two to the power of a count is the iteration, that
many times, of halving, starting from m. The iteration is the natural-number recursor on
the count, with m held fixed, packed by unpaired application of the pairing.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- `Nat.rec`-based iterate of "halve", i.e. `myDivPow2 m ℓ = m / 2 ^ ℓ`
(`myDivPow2_eq`), built via `Nat.Primrec.prec` on the count `ℓ` (params `m` fixed throughout the
recursion), mirroring `primrec_foldCode`'s "iterate a step a data-dependent number of times" idiom. -/
def myDivPow2 (m ℓ : ℕ) : ℕ := Nat.unpaired (fun z n => n.rec z (fun _ ih => ih / 2)) (Nat.pair m ℓ)

end DomainTheory.NeighbourhoodSystems
