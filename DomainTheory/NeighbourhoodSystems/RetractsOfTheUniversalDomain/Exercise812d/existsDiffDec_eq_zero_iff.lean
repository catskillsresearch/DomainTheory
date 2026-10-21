/-ai
For a difference-closed system with no minimal neighbourhood, the difference-existence decider reads zero on a pair exactly when the set difference is empty.

The decider is at most one, reads one exactly when a genuine difference exists, and a genuine difference exists exactly when the difference is nonempty. A zero reading therefore rules out a nonempty difference, and an empty difference rules out a reading of one.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableSplit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableUnion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.diff_exists_iff_ne_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.existsDiffDec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.existsDiffDec_le_one
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.existsDiffDec_spec

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.mem_ne_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union_mem_or_empty
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section DirectDec

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)

variable (hDiff : IsComputableDiff P)

/-- **The `\`-existence decider matches non-emptiness**, via `IsComputableDiff.diff_exists_iff_ne_empty`. -/
theorem existsDiffDec_eq_zero_iff (hdiff : V.DiffClosed) (hnomin : V.NoMinimal) (n m : ℕ) :
    existsDiffDec P hDiff (Nat.pair n m) = 0 ↔ P.X n \ P.X m = ∅ := by
  have hle := existsDiffDec_le_one P hDiff (Nat.pair n m)
  have h1 := existsDiffDec_spec P hDiff n m
  have h2 := IsComputableDiff.diff_exists_iff_ne_empty (P := P) hdiff hnomin n m
  constructor
  · intro h0
    by_contra hne
    have h1' : existsDiffDec P hDiff (Nat.pair n m) = 1 := h1.mpr (h2.mpr hne)
    omega
  · intro hempty
    by_contra hne0
    have h1' : existsDiffDec P hDiff (Nat.pair n m) = 1 := by omega
    exact (h2.mp (h1.mp h1')) hempty

end DirectDec

end DomainTheory.NeighbourhoodSystems
