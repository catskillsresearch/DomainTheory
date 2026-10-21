/-ai
The two-way combination of packed found-flag and code pairs returns the second pair when the first found nothing, returns the first pair when only the first found something, and returns found flag 1 paired with the union of the two codes when both found something.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableSplit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableUnion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx0_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx1_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateJunk_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateInnerC_packStateC

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.mem_ne_empty
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

/-- **Combine two `(found, code)` packed fold results into one**: union their codes via `hUnion`
when both found something, and simply propagate whichever single side found something otherwise
(mirroring `XFoldStep`/`YFoldStep`'s own "skip junk, else union" shape one level up). Generic in any
`IsComputableUnion`, reused below for `YPseqCode`'s "outer 2-way union" of its two `bx`-fixed inner
folds. -/
noncomputable def combineFound2 {γ : Type*} {W : NeighborhoodSystem γ}
    {Q : ComputablePresentation W} (hUnion : IsComputableUnion Q) (r0 r1 : ℕ) : ℕ :=
  selectFn r0.unpair.1
    (selectFn r1.unpair.1 (Nat.pair 1 (hUnion.unionIdx r0.unpair.2 r1.unpair.2)) r0)
    r1

end DomainTheory.NeighbourhoodSystems
