/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.Trianglelefteq
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.IsGen
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.Dprime
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.toEl
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.ofEl
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.dprimeEquiv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.Basic.notation4
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.isGen_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.isGen_exists
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.isGen_mono
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.isGen_mono'
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.isGen_fst_unique
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.isGen_snd_unique
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.isGen_inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.mem_Dprime
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.Dprime_subsystem

@[expose] public section

/-!
# Lecture VI — Lemma 6.15 (Scott 1981, PRG-19): the converse of Proposition 6.12

Proposition 6.12 says a subdomain relation `D ◁ E` yields a *projection pair* `i : D → E`,
`j : E → D` with `j ∘ i = I_D` and `i ∘ j ⊆ I_E`. **Lemma 6.15** is the converse: *any* projection
pair — between two neighbourhood systems `D` and `E` over possibly **different** token types —
exhibits `D` as (isomorphic to) a subdomain of `E`. Scott writes `D ⊴ E` as short for "`D ≅ D'`
for some `D' ◁ E`."

**Lemma 6.15.** If there exist approximable maps `i : D → E` and `j : E → D` with `j ∘ i = I_D`
and `i ∘ j ⊆ I_E`, then `D ⊴ E`.

## The construction (cleaner than Scott's, fully relational)

Scott's proof works with the ideal elements (filters) and shows that `i` carries finite (principal)
elements to finite elements. We avoid the filter-by-filter argument by isolating one relational
predicate:

`IsGen i j X Y := X i Y ∧ Y j X`   ("`Y` generates `i(↑X)`").

Everything follows from three relational facts:

* **`isGen_exists`** (uses `j ∘ i = I_D`): every `X ∈ D` has a generator `Y` (apply `j∘i = I` to the
  identity relation `X I_D X`).
* **`isGen_mono`** (uses `j ∘ i = I_D`) and **`isGen_mono'`** (uses `i ∘ j ⊆ I_E`): the generator
  correspondence is inclusion-monotone in both directions — `Y ⊆ Y' ↔ X ⊆ X'`. Their two-way use
  gives that generators are unique in each argument (`isGen_fst_unique`/`isGen_snd_unique`).
* **`isGen_inter`** (just `mono`/`inter_right` of `i, j`): if `Y, Y'` are generators and `Y ∩ Y' ∈ E`,
  then `Y ∩ Y'` generates `X ∩ X'`.

The image system `Dprime i j` has `Y` as a neighbourhood iff `Y` generates some `X ∈ D`; its master
is `E`'s master. `isGen_inter` makes it a neighbourhood system **and** gives the crucial
`inter_closed` clause of `◁` (consistency inherited from `E`), so `Dprime i j ◁ E`. The
order-isomorphism `D ≅ Dprime i j` is `x ↦ {Y ∣ ∃ X ∈ x, IsGen i j X Y}` with inverse
`y ↦ {X ∣ ∃ Y ∈ y, IsGen i j X Y}`, the inverse laws and order-reflection coming from generator
uniqueness.

Everything is built at the level of Definition 2.1 relations, so the whole development is
**choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}



section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)














end ProjectionPair
end DomainTheory.NeighbourhoodSystems
