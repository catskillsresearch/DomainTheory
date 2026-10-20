/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Definition71
import DomainTheory.Neighborhood.Approximable

/-!
# Definition 7.2 (Scott 1981, PRG-19, §7) — computable maps and computable elements

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19, Lecture VII,
*Computability in effectively given domains*.

> **Definition 7.2.** Given two recursively presented domains `𝒟 = {Xₙ ∣ n ∈ ℕ}` and
> `ℰ = {Yₘ ∣ m ∈ ℕ}`, an approximable mapping `f : 𝒟 → ℰ` is said to be *computable* iff the
> relation `Xₙ f Yₘ` is **recursively enumerable** in `n` and `m`.

Why r.e. (and not recursive)? Scott answers by degenerating `𝒟` to the one-point domain `{Δ}`: then
`f` is just a single element `y = f({Δ}) ∈ |ℰ|`, and the condition reduces to the index set
`{m ∣ Yₘ ∈ y}` being r.e. A *finite* element has a recursive index set, but an infinite element can
only be approximated "a little at a time" — its approximations can be *listed* (r.e.) but membership
need not be decidable. So 7.2 already incorporates the notion of a **computable element**
(`IsComputableElement`).

We model `IsComputableMap` as `REPred₂ (fun n m ↦ Xₙ f Yₘ)` over the choice-free recursion theory of
`Recursive.lean` (`REPred` = projection of a recursively decidable relation; see that file for why we
roll our own and reject Mathlib's classical recursion theory).

**Proposition 7.3** is then formalized in full:

* `idMap_isComputable` — the identity map is computable, because `Xₙ I Xₘ ↔ Xₙ ⊆ Xₘ`
  (`ComputablePresentation.incl_computable`) is recursively *decidable*, hence r.e.
* `comp_isComputable` — the composition of computable maps is computable: `Xₙ (g∘f) Zₖ` is
  `∃ Yₗ, Xₙ f Yₗ ∧ Yₗ g Zₖ` (surjectivity of the middle presentation lets `Y` range over indices
  `l`), which is r.e. by the closure lemmas `REPred.comp`/`REPred.and`/`REPred.proj`.
* `apply_isComputableElement` — Scott's stated consequence: a computable map applied to a computable
  element gives a computable element (`f(x) = {Yₘ ∣ ∃ Xₙ ∈ x, Xₙ f Yₘ}`, again r.e. by the closure
  lemmas).

Two further faithful facts:

* `principal_isComputableElement` — every **finite** (principal) element `↑Xₙ` is computable, since
  its index set `{m ∣ Xₙ ⊆ Xₘ}` is a recursive slice of `incl_computable` (Scott's remark that
  finite elements have recursive index sets).

Everything here is `⊆ {propext, Quot.sound}` (choice-free): it is built only from the choice-free
deciders of Definition 7.1 and the choice-free r.e. layer of `Recursive.lean`.
-/

namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}

/-- **Definition 7.2 (Scott 1981, PRG-19) — computable map.** Relative to computable presentations
`P` of `V` and `Q` of `W`, an approximable map `f : V → W` is *computable* iff its neighbourhood
relation `Xₙ f Yₘ`, transported to the integer indices, is recursively enumerable. -/
def IsComputableMap {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
    (P : ComputablePresentation V) (Q : ComputablePresentation W) (f : ApproximableMap V W) : Prop :=
  REPred₂ (fun n m => f.rel (P.X n) (Q.X m))

/-- **Definition 7.2 (Scott 1981, PRG-19) — computable element.** Specializing to `f : 𝟙 → W`, the
condition becomes: the index set `{m ∣ Yₘ ∈ y}` of the element `y ∈ |W|` is recursively enumerable.
We take this as the definition of a *computable element*. -/
def IsComputableElement {W : NeighborhoodSystem β} (Q : ComputablePresentation W)
    (y : W.Element) : Prop :=
  REPred (fun m => y.mem (Q.X m))

variable {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
end DomainTheory.Neighborhood
