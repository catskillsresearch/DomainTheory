/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Theorem88a.Basic
public import DomainTheory.Neighborhood.Theorem88a.idxSet_nonempty
public import DomainTheory.Neighborhood.Theorem88a.idxSet_eq_iff
public import DomainTheory.Neighborhood.Theorem88a.isomorphic_DprimeU
public import DomainTheory.Neighborhood.Theorem88a.theorem_8_8_a
public import DomainTheory.Neighborhood.Theorem88a.theorem_8_8
public import DomainTheory.Neighborhood.Definition71

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

namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-! ### Finite meets of `idxSet`s, at the `Set` level -/

/-- The `idxSet`-atom of the *positive* constraints `pos`: indices `m` with `Xₘ ⊆ Xᵢ` for every
`i ∈ pos`. (The empty list gives `Set.univ`, matching `genAtom`'s depth-`0` value.) -/
def IPos (pos : List ℕ) : Set ℕ := {m | ∀ i ∈ pos, m ∈ idxSet P.X i}

@[simp] theorem IPos_nil : IPos P [] = Set.univ := by
  ext m; simp [IPos]

/-- **The full atom**: positive constraints `pos` together with negative constraints `neg`
(`¬(Xₘ ⊆ Xⱼ)` for `j ∈ neg`). This is `genAtom (idxSet P.X) Set.univ δ n` for the sign sequence
built from `pos`/`neg`. -/
def DAtom (pos neg : List ℕ) : Set ℕ := IPos P pos ∩ {m | ∀ j ∈ neg, m ∉ idxSet P.X j}

/-! ### The meet-fold: one step, threading an `{ok, idx}`-coded accumulator -/

variable (cons : ℕ → ℕ)

/-- One step of the positive meet-fold. The accumulator `r` codes `(ok, idx)`
(`r.unpair.1 = ok`, `r.unpair.2 = idx`); `i` is the next positive-constraint index. If the fold is
still "ok" and `P`'s consistency decider accepts `(idx, i)`, advance to `P.inter idx i`; otherwise
the fold is permanently "not ok" (accumulator frozen at the last good `idx`, which is discarded by
`meetFold_spec` in that case anyway). -/
def meetStep (r i : ℕ) : ℕ :=
  selectFn (isOne r.unpair.1 * isOne (cons (Nat.pair r.unpair.2 i)))
    (Nat.pair 1 (P.inter r.unpair.2 i)) (Nat.pair 0 r.unpair.2)

/-- **The positive meet-fold**: fold `meetStep` across `pos`, starting from `(ok, idx) = (1,
masterIdx)` (the empty meet is `Δ`, always "ok"). -/
def meetFold (l : List ℕ) : ℕ := l.foldl (meetStep P cons) (Nat.pair 1 P.masterIdx)

@[simp] theorem meetFold_nil : meetFold P cons [] = Nat.pair 1 P.masterIdx := rfl

/-! ### `DAtom` emptiness, reduced to the meet-fold witness and a bounded negative check -/

/-! ### Code-level `meetFold`, and its primitive recursivity -/

/-- `foldCode`-shaped step matching `meetStep`: state `w = pair i (pair r params)` (`params`
unused). -/
def meetStepCode (w : ℕ) : ℕ := meetStep P cons w.unpair.2.unpair.1 w.unpair.1

/-- The code-level positive meet-fold. -/
def meetFoldCode (c : ℕ) : ℕ := foldCode (meetStepCode P cons) 0 (Nat.pair 1 P.masterIdx) c

/-! ### The full decision procedure and its decidability -/

variable (incl : ℕ → ℕ)

/-- **The full `DAtom`-emptiness decider.** `1` iff `DAtom (decodeList posC) (decodeList negC) =
∅`: either the positive meet is already inconsistent (`ok ≠ 1`), or the meet's index `idx` lies
inside some negative target (bounded existential over `decodeList negC`, via `existsListChar`). -/
def DAtomEmptyChar (posC negC : ℕ) : ℕ :=
  selectFn (isOne (meetFoldCode P cons posC).unpair.1)
    (existsListChar (fun t => incl (Nat.pair t.unpair.2 t.unpair.1))
      (meetFoldCode P cons posC).unpair.2 negC)
    1

/-! ### The packaged decidability statement -/
end DomainTheory.Neighborhood
