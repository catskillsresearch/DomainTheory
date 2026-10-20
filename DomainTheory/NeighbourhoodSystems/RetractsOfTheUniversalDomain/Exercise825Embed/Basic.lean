/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise618
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Embed.embedIntoPow

@[expose] public section

/-!
# Exercise 8.25 (Scott 1981, PRG-19, §8), step 3 — `𝒟 ⊴ 𝒟^∞`

Scott's hint remarks that (after solving `D ≅ D → 𝒰^∞`) "`𝒰 ◁ D`", i.e. the universal domain `𝒰`
embeds as a subdomain of the solution `D`, which is what makes the eventual `D` non-trivial and
universal. The link runs through `𝒰 ⊴ 𝒰^∞`: any domain `V` embeds into its own infinite power
`V^∞ = iterSys V` as the "singleton stack" `x ↦ ⟨x, ⊥, ⊥, …⟩`, with `head` as a retraction.

This file proves `V ⊴ iterSys V` for **every** `V` (Lemma 6.15 applied to the projection pair
`embedIntoPow ⊣ head`), reusing the stack combinators `head`/`push`/`pair` from Exercise 5.11 and
the bottom-sequence computation `component_bot` from Exercise 6.18. Specializing `V := 𝒰` gives
Scott's `𝒰 ⊴ 𝒰^∞`.

Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise511

variable {α : Type*} (V : NeighborhoodSystem α)

end DomainTheory.NeighbourhoodSystems
