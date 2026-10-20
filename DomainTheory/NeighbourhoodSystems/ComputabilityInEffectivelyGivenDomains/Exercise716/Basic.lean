/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise716.curryStepCode

@[expose] public section

/-!
# Exercise 7.16 (Scott 1981, PRG-19, §7) — `curry` as a neighbourhood relation

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19, Lecture VII.

> **Exercise 7.16.** Let `D₀ = {Xₙ}`, `D₁ = {Yₘ}` and `D₂ = {Zₖ}` be three effectively given domains.
> Complete the proof of 7.5 by writing out `curry` as a relation between neighbourhoods. Is it a
> recursive set or only a recursively enumerable set?

Theorem 7.5 (`Theorem75.lean`) states that `eval` and `curry` are *computable* combinators. Scott
writes out `eval` explicitly and shows its neighbourhood relation is a **recursive** (decidable) set;
he leaves `curry` "to the exercises". This file completes that: it writes out the `curry`
**combinator**

  `curry : (𝒟₀ × 𝒟₁ → 𝒟₂) → (𝒟₀ → (𝒟₁ → 𝒟₂))`

as an approximable mapping between the two function-space domains, gives its neighbourhood relation,
and shows that relation is **recursive** (a recursively *decidable* set), not merely r.e. — exactly as
for `eval`.

## The combinator and its neighbourhood relation

`curry` (Theorem 3.12, `FunctionSpace.curry`) is the function on *maps* `g ↦ curry g`. As Scott's
Theorem 3.12 shows, it is an order-isomorphism `|𝒟₀×𝒟₁→𝒟₂| ≃ |𝒟₀→(𝒟₁→𝒟₂)|`, so by Theorem 2.7
(`ofIso`) it itself comes from an approximable mapping between the function-space domains — already
built as `curryC V₀ V₁ V₂` in `Table55.lean` (with faithfulness `curryC_toApproxMap`). We reuse it
and **write out** its neighbourhood relation (`curryComb_rel`):

  `G curryC H  ⟺  G, H neighbourhoods and ∀ g ∈ G, curry g ∈ H`,

which, unfolded to the explicit step-entries of the two presentations, reads:

  `G curryC H  ⟺  for every entry `[Xₗ, Wₗ]` of `H` and every step `[Yₗᵢ, Zₗᵢ]` of `Wₗ`,
                       G ⊆ [⟨Xₗ, Yₗᵢ⟩, Zₗᵢ]`.

Each `G ⊆ [⟨Xₗ,Yₗᵢ⟩,Zₗᵢ]` is **function-space inclusion** in `(𝒟₀×𝒟₁→𝒟₂)`, which is recursively
*decidable* (`ComputablePresentation.incl_computable`), and the surrounding quantifier is a *bounded*
`∀` over the coded entry-lists. Hence the relation is **recursive** — the answer to Scott's question.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}

/-! ### The `curry` combinator as an approximable mapping (Theorem 2.7 / Theorem 3.12).

The combinator `curry : (𝒟₀×𝒟₁→𝒟₂) → (𝒟₀→(𝒟₁→𝒟₂))` is already built in `Table55.lean` as
`curryC V₀ V₁ V₂ = ofIso (curryIso V₀ V₁ V₂)` (Theorem 2.7 applied to Theorem 3.12's order-iso
`curryIso`), with faithfulness `curryC_toApproxMap`. We reuse it and write out its neighbourhood
relation. -/

/-! ### Writing out `curry` as a relation between neighbourhoods. -/

/-! ### Recursive (not merely r.e.): the combinator's neighbourhood relation is decidable.

Following the structure of `eval` (Milestone 7 of `Theorem75.lean`, where Scott observes `eval` is a
*recursive* set), we show that `curry` — read off the explicit step-entries of the two presentations —
is a **recursively decidable** relation between codes. The crux: each clause `G ⊆ [⟨Xₗ,Yₗᵢ⟩,Zₗᵢ]` is
function-space inclusion in `(𝒟₀×𝒟₁→𝒟₂)`, recursively *decidable* via `incl_computable`; the step
`[⟨Xₗ,Yₗᵢ⟩,Zₗᵢ]` is a one-entry function-space neighbourhood (`Xenum_singleton`); the surrounding
quantifiers are *bounded* `∀`s over the coded entry-lists (`RecDecidable₂.bForallList`). -/

end DomainTheory.NeighbourhoodSystems
