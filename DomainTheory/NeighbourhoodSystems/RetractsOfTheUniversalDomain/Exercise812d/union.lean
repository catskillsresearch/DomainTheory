module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other_8
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.part_c_2

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718


namespace IsComputableUnion

variable {α : Type*} {V : NeighborhoodSystem α} {P : ComputablePresentation V}

namespace union
/-- **Under `UnionClosed`, the existential is unconditionally true** — every `X n ∪ X m` is a
genuine neighbourhood, hence indexed by `P.surj`. Mirrors
`IsComputableDiff.diff.exists_iff_ne_empty`, but simpler: `∪` has no "-or-empty" branch to rule
out, so this is a plain existence fact rather than an `iff`. Not needed to *state*
`IsComputableUnion` (kept off the structure itself, matching how `DiffClosed`/`UnionClosed` are
separate hypotheses from `ComputablePresentation` elsewhere in this file); recorded here for
convenience, though the eventual `(d)(4)(c)`/`(d)` instantiation is expected to discharge
`unionIdx_spec`'s hypothesis directly from `XPseq.mem`/`YPseq.mem`-style facts specific to the
atoms actually in play, rather than from a blanket `UnionClosed` on all of `D`. -/
theorem «exists» (hunion : V.UnionClosed) (n m : ℕ) :
    ∃ k, P.X k = P.X n ∪ P.X m :=
  P.surj (hunion (P.mem_X n) (P.mem_X m))

end union
end IsComputableUnion
end DomainTheory.NeighbourhoodSystems
