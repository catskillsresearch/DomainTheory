/-ai
This file gathers and re-exports the definitions used to decide emptiness of a D-side atom in an effectively presented neighbourhood system: the positive index set and the atom, the meet step and the meet-fold together with their code-level versions, the emptiness characteristic, and the empty-list cases of the positive index set and the meet-fold.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.idxSet_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.idxSet_eq_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.isomorphic_DprimeU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.theorem_8_8_a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.theorem_8_8
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.IPos
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.DAtom
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.meetStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.meetFold
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.meetStepCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.meetFoldCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.DAtomEmptyChar
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.IPos_nil
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.meetFold_nil

@[expose] public section

/-!
# Theorem 8.8(b), Part 5 — decidable `D`-side atom emptiness

`Theorem88.lean`/`Theorem88a.lean` build Scott's back-and-forth construction for the *general*
(non-effective) Theorem 8.8(a): at each step, `exists_split` classically case-splits on whether a
`D`-side atom `A` (or `A ∩ Xₙ`, `A \ Xₙ`) is empty. For the *effective* refinement (8.8(b)) we need
this decided, not merely known, from an explicit `ComputablePresentation P` of `D`.

## The `idxSet` reindexing, revisited

Following `Theorem88a.lean`'s key idea, we track atoms not as literal subsets of `α` (arbitrary
Boolean combinations of `D`-neighbourhoods, generally *not* themselves `D`-neighbourhoods) but as
subsets of the *index set* `ℕ`, via `idxSet P.X n = {m ∣ Xₘ ⊆ Xₙ}`. A finite sign-constraint atom
is then

```
DAtom pos neg := {m ∣ (∀ i ∈ pos, Xₘ ⊆ Xᵢ) ∧ (∀ j ∈ neg, ¬ (Xₘ ⊆ Xⱼ))}
```

for two lists `pos, neg : List ℕ` of `D`-indices (the "+" and "−" targets so far). This is
*exactly* `genAtom (idxSet P.X) Set.univ δ n` for the sign sequence `δ` matching `pos`/`neg`.

## Why this is decidable (and the general `(♦)`-style union trick is not needed)

The positive part's (non-)emptiness reduces to *iterated pairwise consistency*: fold `P.inter`
across `pos`, checking `P`'s own consistency decider (`cons_computable`) at each step
(`meetFold`/`meetStep`). This produces a `{ok, idx}` pair: `ok = 1` iff `{Xᵢ ∣ i ∈ pos}` is jointly
witnessed-consistent, in which case `idx` indexes the *exact* meet `⋂_{i ∈ pos} Xᵢ`
(`meetFold_spec`, generalizing `idxSet_inter_of_inter_eq` along the fold).

Given that, the *negative* constraints are handled with no extra machinery at all: `idx` is the
**greatest** index satisfying every positive constraint (`Xₘ ⊆ Xᵢ` for `i ∈ pos` forces
`Xₘ ⊆ X_idx`, by construction of the meet), so

* if `X_idx ⊆ Xⱼ` for *some* `j ∈ neg`, **every** candidate `m` inherits `Xₘ ⊆ X_idx ⊆ Xⱼ`, so the
  full atom (positive *and* negative constraints) is empty;
* otherwise `idx` itself already satisfies every negative constraint (`¬(X_idx ⊆ Xⱼ)` for all
  `j ∈ neg`, directly checked), so `idx` witnesses the atom is non-empty.

So `DAtom pos neg` is empty iff `ok ≠ 1` **or** `X_idx ⊆ Xⱼ` for some `j ∈ neg` — a bounded check
against `P`'s own `incl_computable`, decidable with no union/positivity lemma needed
(`DAtom_eq_empty_iff`). This is packaged as `Nat.Primrec` (`DAtomEmptyChar`) and, finally, as
`RecDecidable₂` (`DAtom_recDecidable`), extracting `P`'s two deciders inside the (`Prop`-valued)
`RecDecidable₂` goal — choice-free, following the `PDPresentation`/`PowerDomain_isEffectivelyGiven`
pattern of `Proposition710.lean`.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-! ### Finite meets of `idxSet`s, at the `Set` level -/




/-! ### The meet-fold: one step, threading an `{ok, idx}`-coded accumulator -/

variable (cons : ℕ → ℕ)




/-! ### `DAtom` emptiness, reduced to the meet-fold witness and a bounded negative check -/

/-! ### Code-level `meetFold`, and its primitive recursivity -/



/-! ### The full decision procedure and its decidability -/

variable (incl : ℕ → ℕ)


/-! ### The packaged decidability statement -/
end DomainTheory.NeighbourhoodSystems
