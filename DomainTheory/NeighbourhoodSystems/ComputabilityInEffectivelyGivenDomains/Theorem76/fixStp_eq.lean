/-ai
The packed fixed-point step on the pairing of the current index with the pairing of the accumulator and the parameter equals the pure step.

Unfold both sides and unpack the nested pairing.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}


variable (P : ComputablePresentation V)


theorem fixStp_eq (fincl : ℕ → ℕ) (c acc x : ℕ) :
    fixStp fincl (Nat.pair x (Nat.pair acc c)) = fixPStep fincl c acc x := by
  unfold fixStp fixPStep
  simp only [unpair_pair_fst, unpair_pair_snd]

end DomainTheory.NeighbourhoodSystems
