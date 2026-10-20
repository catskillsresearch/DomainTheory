/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41

@[expose] public section

/-!
# Exercise 4.20 (Scott 1981, PRG-19, Lecture IV)

For approximable `f, g : 𝒟 → 𝒟` prove that

  `fix(f ∘ g) = f(fix(g ∘ f))`.

In this development `f ∘ g` is `f.comp g`, whose elementwise action is
`f.toElementMap ∘ g.toElementMap` (`toElementMap_comp`). The least fixed point of an endomap is
`fixElement` (Theorem 4.1), with its fixed-point equation `toElementMap_fixElement` and its
least-pre-fixed-point characterization `fixElement_le_of_toElementMap_le`.

The proof is the classical "rolling rule" / dinaturality of the fixed-point operator:
`f(fix(g ∘ f))` is a fixed point of `f ∘ g`, hence `⊒` the least one, and a symmetric argument
gives the reverse inclusion. Everything stays at the level of `V.Element`, so the whole file is
**choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap
end ApproximableMap
end DomainTheory.NeighbourhoodSystems
