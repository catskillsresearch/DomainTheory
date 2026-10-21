/-ai
This file gathers and re-exports the code-level atom recursion and Y-sequence code, the bit encoding of a finite sign prefix, the coded sets and the neighbourhood system D'' they generate, the pushforward, pullback, and order isomorphism with D, the emptiness core and finite-constraint transfer lemmas between index sets and those coded sets, the embedding comparisons and intersection-index lemmas, the subsystem relation into the universal system, and the decidability and intersection data of the computable presentation of D''.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.mem_decodeQPairList_appendCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.presentedIntervals_decodeQPairList_appendCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.primrec_unionUX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.U_mem_union_UX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.UX_unionUX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.primrec_wY
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.primrec_wState
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.primrec_stateRem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.primrec_statePos
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.primrec_stateNeg
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.primrec_stateCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.primrec_atomBase
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.primrec_atomStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.primrec_datomDec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.datomDec_eq_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.primrec_atomUCodeState
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.primrec_atomUPos
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.primrec_atomUNeg
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.primrec_atomUCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUEmpty_congr
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.deltaOf_mod_two_pow_of_lt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.primrec_atomUEmpty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.primrec_yFoldStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.yFold_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.yFold_succ
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.primrec_yFold
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUEmpty_zero_or_one
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.yFoldStep_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.yFold_found_le_one
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.yFold_found_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.yFold_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.yFold_two_pow_found
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.primrec_YseqCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.mem_UX_YseqCode_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_succ_true
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.eq_of_deltaOf_agree_of_lt_two_pow
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_disjoint_YseqCode_of_posTwin_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCodeState_congr_twin
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_succ_false
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.DAtom_union
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_eq_genAtomYseqCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_inter_succ_empty_of_junk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.genAtom_Yc_empty_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88c.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88c.DprimeU_isEffectivelyGiven
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.encodeBits
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.DprimeUCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.toDprimeUCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.toDCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.domainIsoCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.DprimeUCodePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.Yc_subset_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.Yc_zero_eq_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.encodeBits_lt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.deltaOf_encodeBits
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.hcoreIdxYc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.transfer_dir_idxYc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.transfer_empty_iff_idxYc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.transfer_subset_iff_idxYc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.transfer_inter_empty_iff_idxYc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.transfer_double_subset_iff_idxYc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.embed_subset_iff_code
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.embed_eq_iff_code
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.embed_subset_iff_raw_code
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.embed_eq_iff_raw_code
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.transfer_inter_eq_iff_idxYc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.exists_inter_index_of_dmem_code
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.exists_inter_index_of_nonempty_code
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.DprimeUCode_subsystem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.inclK_i_recDecidable_code
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.inclK_j_recDecidable_code
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.DprimeUCode_interEq_computable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.DprimeUCode_cons_computable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.DprimeUCode_inter_spec

@[expose] public section

/-!
# Theorem 8.8(b)(vii)(3) — a genuinely code-driven subsystem `D''`

`Theorem88d.lean` (Part 7) builds a fully `Nat.Primrec` back-and-forth recursion — `atomUCode`/
`YseqCode` — tracking `U`-codes natively, and proves the two halves of Scott's matching invariant
at the code level: validity (`atomUCode_mem`, free) and the emptiness-match
(`genAtom_Yc_empty_iff`, where `Yc P n := UX (YseqCode P n)`). This file finishes the job Scott's
own Theorem 8.8(a)/(b) Part 6 (`Theorem88a.lean`/`Theorem88c.lean`) already did for the *classical*
`Yidx (e P)` — but for `Yc P` instead, which is **genuinely code-driven**: unlike `Yidx`, whose
*value* is whatever `Classical.choice` happened to pick, `Yc P n = UX (YseqCode P n)` is *literally*
`UX` applied to a `Nat.Primrec` function of `n` and `P`'s own deciders.

## Plan

* Port the finite-constraint transfer lemmas (`Theorem88.lean`'s `transfer_dir`/`transfer_empty_iff`
 /`transfer_subset_iff`/`transfer_inter_eq_iff`) to the pair `(idxSet (e P), Set.univ)` vs.
 `(Yc P, U.master)`, using `genAtom_Yc_empty_iff` (plus `encodeBits`, realizing any finite prefix of
 an arbitrary `δ : ℕ → Bool` as some `deltaOf k`) as the emptiness-matching core, in place of
 `atomU_invariant`/`atomU_eq_genAtom`.
* Assemble `D'' := DprimeUCode`, `D ≅ᴰ D''`, `D'' ◁ U` — mirroring `Theorem88a.lean`'s
 `DprimeU`/`domainIso`/`DprimeU_subsystem` verbatim, with `Yidx (e P) ↦ Yc P` and the transfer
 lemmas above in place of `Theorem88.lean`'s generic ones.
* Build `ComputablePresentation D''` with `X n := Yc P n`, master index `0` — mirroring
 `Theorem88c.lean`'s `DprimeUPresentation`, reusing `idxSet_inter_eq_iff_DAtom`/
 `DAtom_pair_recDecidable`/`(P0 P).incl_computable`/`(P0 P).cons_computable`/`(P0 P).inter`
 unchanged (the *index relations* were already decidable; only the *carrier family* changes).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-! ## `Yc P`'s basic facts: subset-of-master and the zero-depth base case -/


/-! ## Realizing any finite `δ`-prefix as `deltaOf k` for some `k`

`genAtom_Yc_empty_iff` only relates `genAtom` at sign sequences of the special form `deltaOf k`.
The general finite-constraint transfer lemma (`transfer_dir`, below) needs the emptiness match for
*every* `δ : ℕ → Bool`. Since `genAtom Z M δ n` only inspects `δ 0, …, δ (n - 1)` (`genAtom_congr`),
it suffices to realize any finite prefix of `δ` as `deltaOf k` for a suitable `k < 2 ^ n`. -/


/-! ## Porting `Theorem88.lean`'s finite-constraint transfer lemma to `(idxSet (e P), Yc P)`

`transfer_dir` (private in `Theorem88.lean`) is stated fully generically over any two families
related by a `genAtom`-emptiness core — exactly `hcoreIdxYc` above — so it is reproduced verbatim
here (there is nothing to prove beyond what `Theorem88.lean` already established once and for all;
only the *instantiation* differs). -/


/-! ## Assembling `D'' := DprimeUCode`, `D ≅ᴰ D''`, and `D'' ◁ U`

Mirrors `Theorem88a.lean`'s `DprimeU`/`domainIso`/`DprimeU_subsystem`/`isomorphic_DprimeU` verbatim,
with `Yidx (e P) ↦ Yc P` and `exists_inter_index_of_dmem`/`exists_inter_index_of_nonempty`'s calls
to `transfer_inter_eq_iff`/`transfer_inter_empty_iff` (generic, `Yseq`-flavoured) replaced by the
`Yc`-flavoured `transfer_inter_eq_iff_idxYc`/`transfer_inter_empty_iff_idxYc` above. -/


/-! ## The element-level isomorphism `D ≅ᴰ D''` -/


/-! ## Building `ComputablePresentation D''`

Mirrors `Theorem88c.lean`'s `DprimeUPresentation` verbatim, with `Yidx (e P) ↦ Yc P` and the
generic `transfer_inter_eq_iff`/`embed_subset_iff` replaced by the `Yc`-flavoured
`transfer_inter_eq_iff_idxYc`/`embed_subset_iff_raw_code` above. The two index relations
(`interEq_computable`, `cons_computable`) and the intersection index (`inter`) are **reused
unchanged** from `(P0 P)` — only the carrier family (`Yidx` ↦ `Yc P`, now genuinely code-driven)
changes; `idxSet_inter_eq_iff_DAtom`/`DAtom_pair_recDecidable` (Theorem88c.lean, stated generically
for any `ComputablePresentation Q`) apply verbatim to `Q := P0 P`. -/


end DomainTheory.NeighbourhoodSystems
