module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableSplit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableUnion

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.mem_ne_empty
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

namespace IsComputableDiff

variable {α : Type*} {V : NeighborhoodSystem α} {P : ComputablePresentation V}

/-- **The emptiness/genuineness dichotomy**, transported through `DiffClosed` +
`NoMinimal.mem_ne_empty`: for a `DiffClosed`, `NoMinimal` system, "`X n \ X m` is a genuine
neighbourhood" and "`X n \ X m` is non-empty" are the *same* proposition — so `diff_computable`
may equally be read as an emptiness decider. Not needed to *state* `IsComputableDiff` (kept off
the structure itself, matching how `DiffClosed`/`NoMinimal` are separate hypotheses from
`ComputablePresentation` elsewhere in this file), but recorded here once for later sub-parts to
reuse directly instead of re-deriving. -/
theorem diff_exists_iff_ne_empty (hdiff : V.DiffClosed) (hnomin : V.NoMinimal) (n m : ℕ) :
    (∃ k, P.X k = P.X n \ P.X m) ↔ P.X n \ P.X m ≠ ∅ := by
  constructor
  · rintro ⟨k, hk⟩ hempty
    exact NoMinimal.mem_ne_empty hnomin (P.mem_X k) (hk.trans hempty)
  · intro hne
    rcases hdiff (P.mem_X n) (P.mem_X m) with hempty | hmem
    · exact absurd hempty hne
    · exact P.surj hmem

end IsComputableDiff

end DomainTheory.NeighbourhoodSystems
