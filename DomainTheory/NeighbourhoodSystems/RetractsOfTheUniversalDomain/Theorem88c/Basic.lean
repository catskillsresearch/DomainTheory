/-ai
This file gathers and re-exports the effective presentation of the subsystem from Theorem 8.8(a): the codes of the two-element positive list and the singleton negative list, the equations and primitive recursiveness of those codes, the characterization of an index-set intersection by a D-atom, the recursive decidability of the two inclusions and of the two-point D-atom, the recursive decidability of the intersection and consistency relations for the transferred neighbourhoods, the transferred intersection index, and the computable presentation of that subsystem.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.he0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.hcover
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.genAtom_empty_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88c.capPosCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88c.capNegCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88c.DprimeUPresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88c.idxSet_inter_eq_iff_DAtom
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88c.capPosCode_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88c.capNegCode_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88c.primrec_capPosCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88c.primrec_capNegCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88c.DAtom_pair_recDecidable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88c.inclK_i_recDecidable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88c.inclK_j_recDecidable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88c.DprimeU_interEq_computable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88c.DprimeU_cons_computable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88c.DprimeU_inter_spec

@[expose] public section

/-!
# Theorem 8.8(b), Part 6d/6e — `D'` (Theorem 8.8(a)'s own subsystem) is effectively given

`Theorem88b.lean` (Part 6a–6c) reduces `genAtom (idxSet e)`-emptiness to `DAtom`-emptiness, which
Part 5 (`DAtomDecidable.lean`) already decides. The original Part 6d/6e plan tried to go one step
further: build an explicit, *computable* replacement `splitEff` for `splitChoice` (Theorem 8.8(a)'s
classical splitting operation), tracking a `U`-code `atomUCode` alongside the abstract `Set`-level
recursion, so that `Yidx e n` itself could be read off as an explicit `U`-code. That plan hit a
genuine wall (recorded in `HANDOFF.md`'s "design pitfall" entry): `SplitU.lean`'s `splitULeft`/
`splitURight` split against the *specific* code fed in (via `canonCode`'s first pair), not against
the *set* `B` alone, and two different codes for the same set can canonicalize to different first
pairs — so there is no way to make an abstract, `Set`-valued `splitEff` agree, code-for-code, with
an independently-built primitive-recursive tracker without first building a genuine canonical-form
(sort+merge) normalization of `List (ℚ × ℚ)`, a substantial undertaking of its own.

## The resolution: never compute `Yidx e n`'s value as a code at all

**The key realization**: `ComputablePresentation`'s `X : ℕ → Set α` field is *data*, not required to
be "computable" as a function producing explicit codes (`unitPresentation`'s constant `X _ := Set.univ`
is the existing sanity check for this). All that must be *decidable* are the two **index relations**
(`interEq_computable`, `cons_computable`) and the primitive-recursive `inter` index function. So
instead of computing `Yidx e n`'s value, we show its *index relations* reduce directly to facts
already decided by Parts 5–6c, via `Theorem88.lean`'s existing generic transfer lemmas — with **no
new splitting operation, no canonical forms, and no exponential atom-union machinery** needed:

* `Yidx e i ∩ Yidx e j = Yidx e k` transfers (`transfer_inter_eq_iff`) to `idxSet e i ∩ idxSet e j =
  idxSet e k`, which unfolds (`idxSet_inter_eq_iff_DAtom`) to `(e k ⊆ e i) ∧ (e k ⊆ e j) ∧
  (DAtom (P0 P) [i, j] [k] = ∅)` — three small, fixed-size decidable facts (two `incl_computable`
  queries, one `DAtom_recDecidable` query at 2-element/1-element lists).
* `∃ k, Yidx e k ⊆ Yidx e i ∩ Yidx e j` transfers (`embed_subset_iff`, twice) to `∃ k, e k ⊆ e i ∧
  e k ⊆ e j`, which is *literally* `(P0 P).cons_computable`'s own predicate — reused verbatim.
* The intersection index itself is *literally* `(P0 P).inter n m` (Scott's own index, reused): its
  correctness transfers via `idxSet_inter_of_inter_eq` + `transfer_inter_eq_iff`.
* The master index is `0` (`Yidx_zero`, already proved in `Theorem88a.lean`).

This packages into `DprimeUPresentation`, a genuine `ComputablePresentation (DprimeU D (e P) …)` —
i.e. **Theorem 8.8(a)'s own `D'` (no new construction!) is effectively given whenever `D` is**. This
completes Part 6 of Theorem 8.8(b): the recursive `Yₙ`-chain now has a certified effective
witness/verifier (its index relations are decidable), ready for Part 7's `ComputableMap` work on
the embedding/projection pair `Subsystem.inj`/`Subsystem.proj` (`D' ◁ U`, via `DprimeU_subsystem`).

Everything here is **choice-free at the `Nat.Primrec` core** (the deciders extracted from
`(P0 P).cons_computable`/`incl_computable`/`DAtom_recDecidable` are plain primitive-recursive
functions); the presentation's `X`-field itself (`Yidx e`) is unavoidably classical (built via
`splitChoice`), exactly like `unitPresentation`'s trivial `X` field is "just data".
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-! ## A general `idxSet`/`DAtom` fact: 2-point atom emptiness characterizes `idxSet`-intersection -/


/-! ## Packaging `DAtom (P0 P) [i, j] [k] = ∅` as a `RecDecidable₃` -/


/-! ## `Yidx`'s index relations are decidable -/


/-! ## Assembling the `ComputablePresentation` -/

end DomainTheory.NeighbourhoodSystems
