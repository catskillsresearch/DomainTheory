module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.Basic

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.mem_ne_empty
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718


namespace IsComputableUnion

variable {α : Type*} {V : NeighborhoodSystem α} {P : ComputablePresentation V}

/-- **Under `UnionClosed`, the existential is unconditionally true** — every `X n ∪ X m` is a
genuine neighbourhood, hence indexed by `P.surj`. Mirrors
`IsComputableDiff.diff_exists_iff_ne_empty`, but simpler: `∪` has no "-or-empty" branch to rule
out, so this is a plain existence fact rather than an `iff`. Not needed to *state*
`IsComputableUnion` (kept off the structure itself, matching how `DiffClosed`/`UnionClosed` are
separate hypotheses from `ComputablePresentation` elsewhere in this file); recorded here for
convenience, though the eventual `(d)(4)(c)`/`(d)` instantiation is expected to discharge
`unionIdx_spec`'s hypothesis directly from `XPseq_mem`/`YPseq_mem`-style facts specific to the
atoms actually in play, rather than from a blanket `UnionClosed` on all of `D`. -/
theorem union_exists (hunion : V.UnionClosed) (n m : ℕ) :
    ∃ k, P.X k = P.X n ∪ P.X m :=
  P.surj (hunion (P.mem_X n) (P.mem_X m))

end IsComputableUnion
end DomainTheory.NeighbourhoodSystems
