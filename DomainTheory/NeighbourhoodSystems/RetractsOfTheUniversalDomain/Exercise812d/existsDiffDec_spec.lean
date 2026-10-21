/-ai
The difference-existence decider reads one on a pair exactly when some enumerated neighbourhood equals the set difference of the two codes.

Unfold the decider and rewrite by the one-indicator. The chosen specification of the computable difference predicate, after the pair is unpacked, is that equivalence.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableSplit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableUnion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.existsDiffDec

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section DirectDec

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)

variable (hDiff : IsComputableDiff P)

theorem existsDiffDec_spec (n m : ℕ) :
    existsDiffDec P hDiff (Nat.pair n m) = 1 ↔ ∃ k, P.X k = P.X n \ P.X m := by
  unfold existsDiffDec
  rw [isOne_eq_one_iff]
  have h := hDiff.diff_computable.choose_spec.2 (Nat.pair n m)
  dsimp only at h
  rw [unpair_pair_fst, unpair_pair_snd] at h
  exact h.symm

end DirectDec

end DomainTheory.NeighbourhoodSystems
