/-ai
This file gathers and re-exports the constructions assembling a computable presentation of the neighbourhood system U: clipping of rational pairs, canonical presenting lists and their codes, the enumeration, intersection and the master index, the presentation itself, and the supporting facts on presented intervals, decoding, primitive recursiveness, membership, surjectivity, and Scott's two relations.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.qpClip
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonList
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.qpClipCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonFilterStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonListCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.masterPairCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.UX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.Uinter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.UmasterIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.presentedIntervals_map_qpClip
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.presentedIntervals_filter_qpPos
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonList_eq_of_filter_eq_nil
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonList_eq_of_filter_eq_cons
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.U_mem_presentedIntervals_canonList
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonList_fixed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.primrec_qpClipCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.decodeRatPair_qpClipCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.primrec_canonFilterStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.decodeList_canonFilterStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.primrec_canonListCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.decodeQPairList_canonFilterStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.mem_decodeQPairList_canonFilterStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.mem_decodeQPairList_canonListCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.presentedIntervals_decodeQPairList_canonListCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.presentedIntervals_eq_empty_iff_of_forall_lt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.decodeQPairList_canonListCode_eq_nil_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.decodeRatPair_masterPairCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.decodeQPairList_masterCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.primrec_canonCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.presentedIntervals_decodeQPairList_canonCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.UX_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.U_mem_UX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.U_surj_UX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.U_cons_iff_nonempty_inter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.U_interEq_computable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.U_cons_computable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.Uinter_primrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.Uinter_spec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.presentedIntervals_singleton_zero_one
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.UX_UmasterIdx

@[expose] public section

/-!
# Theorem 8.8(b), Part 3 — `𝒰` (Definition 8.7) has a genuine `ComputablePresentation`

Assembles `Definition71.lean`'s `ComputablePresentation U` from `IntervalPrimrec.lean`'s code-level
interval arithmetic and decidability results, proving `U.IsEffectivelyGiven`.

## The enumeration

Every natural `c` codes a `List (ℚ × ℚ)` (`decodeQPairList`), but not every such list presents a
genuine `U`-neighbourhood (it may be empty, or stray outside `[0,1)`). `canonList` **canonicalizes**
an arbitrary list to one that does: clip every pair into `[0,1)` (`qpClip`, mirroring
`Definition87.lean`'s private `clip`) and discard now-degenerate pairs, falling back to the single
pair `(0,1)` (presenting `U.master`) if nothing survives. `canonList_fixed` is the key reuse lemma:
canonicalizing a list that **already** presents a `U`-neighbourhood changes nothing (as a set) — this
drives both `surj` (every `U`-neighbourhood has a Scott-literal presenting list, by `U_mem_iff_scott`,
on which `canonList` is a no-op) and `inter_spec` (the raw `combineCode` output, when non-empty, is
already a `U`-neighbourhood, so re-canonicalizing it is also a no-op).

`canonCode` mirrors `canonList` at the `Nat.Primrec` level (`canonListCode` performs the clip/filter
via `RecursiveCross.lean`'s `flatMapCode`; a final `selectFn`/`isZero` test supplies the `(0,1)`
fallback), with `presentedIntervals_decodeQPairList_canonCode` bridging the two. `X n :=
presentedIntervals (decodeQPairList (canonCode n))` is then `𝒰`'s enumeration, and Scott's two
relations reduce directly to `IntervalPrimrec.lean`'s `recDecidable₂_presentedIntervals_eq`/
`recDecidable_presentedIntervals_nonempty` (intersection is a *raw* `combineCode`, and — since `U`
is so permissive — is automatically a genuine `U`-neighbourhood whenever it is non-empty, so
"consistent" reduces to "non-empty").
-/

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-! ### List-level canonicalization -/


/-! ### Code-level canonicalization: `canonCode` -/


/-! ### Assembling `U.ComputablePresentation` -/


end DomainTheory.NeighbourhoodSystems
