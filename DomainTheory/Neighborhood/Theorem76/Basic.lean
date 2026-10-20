/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem75
import DomainTheory.Neighborhood.Theorem41

/-!
# Theorem 7.6 (Scott 1981, PRG-19, §7) — `fix : (𝒟 → 𝒟) → 𝒟` is computable

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19, Lecture VII.

> **Theorem 7.6.** For any effectively given domain `𝒟`, the combinator `fix : (𝒟 → 𝒟) → 𝒟` is
> computable.

Scott's proof reads off the neighbourhood relation of `fix` from the fixed-point construction of
Theorem 4.1/4.2: writing `𝒟 = {Xₙ}` effectively given,

  `⋂_{i<q} [X_{nᵢ}, X_{mᵢ}] fix X_ℓ` iff for some finite sequence `Δ = X_{k₀}, …, X_{k_p} = X_ℓ`
  we have, for each `j < p`, `⋂{ X_{mᵢ} ∣ X_{kⱼ} ⊆ X_{nᵢ} } ⊆ X_{kⱼ₊₁}`.

Inside "for some finite sequence" all the checks are *decidable* (by the effective presentation), and
the existential quantification of a decidable predicate is recursively enumerable. (Since there is no
bound on the length of the sequence, this is genuinely r.e. and not generally recursive.)

## Strategy (choice-free)

The function-space neighbourhood `F = Xenum c` (Theorem 7.5) is a finite intersection
`⋂[X_{nᵢ}, X_{mᵢ}]`; its *least map* is `ĝ = toApproxMap (↑F)`, and `(fix V).rel F (X_ℓ)` unfolds via
`rel_iff_mem_principal` + `fixMap_toElementMap` + `mem_fixElement` to

  `∃ p, (ĝᵖ).rel Δ (X_ℓ)`.

The one-step relation `ĝ.rel (X_a) (X_b) ↔ F ⊆ [X_a, X_b]` is exactly Scott's
`⋂{X_{mᵢ} ∣ X_a ⊆ X_{nᵢ}} ⊆ X_b`, and — crucially — it is **recursively decidable**, because
`[X_a, X_b] = Xenum (codePair a b)` (a one-entry, always-consistent function-space neighbourhood) so
the test is the decidable function-space inclusion `Xenum c ⊆ Xenum (codePair a b)`
(`funPresentation.incl_computable`, Theorem 7.5).

We model a finite `ĝ`-chain by a **list of indices** (using `surj` to name each intermediate
neighbourhood) and prove the characterisation `(fix V).rel (Xenum c) (X_ℓ) ↔ ∃ full, gStepsOK …`
(soundness/completeness over the list, choice-free). The existential over the list is then realised
as the r.e. `∃ i, q (pair i n)`, where `q` decodes `i` to the chain, runs a single primitive-recursive
`foldCode` (`fixChainChar`) threading the previous index and a `{0,1}` consistency flag, and checks
the flag together with the final inclusion `X_{last} ⊆ X_ℓ`. Everything audits
`⊆ {propext, Quot.sound}`.
-/

namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

/-! ### A finite `g`-chain over presentation indices.

`gStepsOK g P a full` says: starting from the index `a`, the consecutive `g`-steps along the index
list `full` all hold, and `gLastOf a full` is the final index reached. -/

/-- The last index of the chain `a, full₀, full₁, …`. -/
def gLastOf : ℕ → List ℕ → ℕ
  | a, [] => a
  | _, (b :: rest) => gLastOf b rest

/-- The consecutive `g`-steps `g.rel (X_a) (X_{full₀})`, `g.rel (X_{full₀}) (X_{full₁})`, … all hold. -/
def gStepsOK (g : ApproximableMap V V) (P : ComputablePresentation V) : ℕ → List ℕ → Prop
  | _, [] => True
  | a, (b :: rest) => g.rel (P.X a) (P.X b) ∧ gStepsOK g P b rest

/-! ### The least map of `Xenum c` and its decidable one-step relation. -/

/-- The one-entry function-space code: `Xenum (codePair a b) = [X_a, X_b]`. -/
def codePair (a b : ℕ) : ℕ := Nat.pair (Nat.pair a b) 0 + 1

variable (P : ComputablePresentation V)

/-! ### The decidable chain predicate and its primitive-recursive `foldCode`. -/

/-- The decidable mirror of `gStepsOK`, phrased with the function-space inclusion char `fincl`. -/
def chainDec (fincl : ℕ → ℕ) (c : ℕ) : ℕ → List ℕ → Prop
  | _, [] => True
  | a, (b :: rest) => fincl (Nat.pair c (codePair a b)) = 1 ∧ chainDec fincl c b rest

/-- One packed `foldCode` step: state `pair acc params` with `acc = pair prev flag`, current element
`x`. Updates the flag with the one-step consistency test and advances `prev` to `x`. -/
def fixStp (fincl : ℕ → ℕ) (w : ℕ) : ℕ :=
  Nat.pair w.unpair.1
    (selectFn w.unpair.2.unpair.1.unpair.2
      (isOne (fincl (Nat.pair w.unpair.2.unpair.2
        (codePair w.unpair.2.unpair.1.unpair.1 w.unpair.1)))) 0)

/-- The pure left-fold step corresponding to `fixStp` (parameter `c`, accumulator `acc = pair prev
flag`, current element `x`). -/
def fixPStep (fincl : ℕ → ℕ) (c acc x : ℕ) : ℕ :=
  Nat.pair x (selectFn acc.unpair.2 (isOne (fincl (Nat.pair c (codePair acc.unpair.1 x)))) 0)

/-- The chain `foldCode`: starts from `pair masterIdx 1`, threads the parameter `c`, over the list
coded by `i`. Returns `pair lastIdx flag`. -/
def fixChainChar (fincl : ℕ → ℕ) (c i : ℕ) : ℕ :=
  foldCode (fixStp fincl) c (Nat.pair P.masterIdx 1) i
end DomainTheory.Neighborhood
