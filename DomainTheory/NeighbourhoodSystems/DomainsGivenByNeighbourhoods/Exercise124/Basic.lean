/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Basic
public import Mathlib.Order.Zorn
import all Mathlib.Order.Zorn
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

/-!
# Exercise 1.24 (Scott 1981, PRG-19, §1) — every partial element extends to a total one (AC)

Scott (for set theorists): using the Axiom of Choice, prove that in every domain a partial element
can always be extended to a total element. (Hint: the union of every transfinite chain of filters
is again a filter.)

This file formalizes:

* `chainUnion C hne hchain` — the union `⋃ C` of a non-empty **chain** `C` of filters is itself a
  filter (`V.Element`); the only non-trivial axiom is `inter_mem`, which uses chain-directedness to
  find a single member of `C` containing both factors. Plus `le_chainUnion` (every member of the
  chain is `⊑` the union).
* `exists_total_ge x` — **with Zorn's lemma** (`zorn_le_nonempty_Ici₀`), every element `x` has a
  *total* element `t` above it (`x ⊑ t ∧ IsTotal t`). The chains in `Ici x` are bounded above by
  their `chainUnion`, so Zorn produces a maximal — i.e. total — element.

Whether this is *equivalent* to AC is left as prose (Scott's question); we do not formalize the
reversal. This is the explicitly **classical** exercise: `exists_total_ge` legitimately uses
`Classical.choice` through `zorn_le_nonempty_Ici₀`. The `chainUnion` *construction* is choice-free
(`[propext, Quot.sound]`). -/

namespace DomainTheory.Neighborhood

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Exercise 1.24 — the union of a chain of filters is a filter.** For a non-empty chain `C` of
filters, `⋃ C = {X ∣ ∃ x ∈ C, X ∈ x}` is again a filter. The intersection axiom uses chain
totality: given `X ∈ x` and `Y ∈ y` with `x, y ∈ C`, one of `x ⊑ y`, `y ⊑ x` holds, and the larger
filter contains both `X` and `Y`, hence `X ∩ Y`. -/
def chainUnion (C : Set V.Element) (hne : C.Nonempty) (hchain : IsChain (· ≤ ·) C) : V.Element where
  mem X := ∃ x ∈ C, x.mem X
  sub := by rintro X ⟨x, _, hxX⟩; exact x.sub hxX
  master_mem := by obtain ⟨x, hxC⟩ := hne; exact ⟨x, hxC, x.master_mem⟩
  inter_mem := by
    rintro X Y ⟨x, hxC, hxX⟩ ⟨y, hyC, hyY⟩
    rcases hchain.total hxC hyC with hxy | hyx
    · exact ⟨y, hyC, y.inter_mem (hxy X hxX) hyY⟩
    · exact ⟨x, hxC, x.inter_mem hxX (hyx Y hyY)⟩
  up_mem := by
    rintro X Y ⟨x, hxC, hxX⟩ hY hXY
    exact ⟨x, hxC, x.up_mem hxX hY hXY⟩
end NeighborhoodSystem
end DomainTheory.Neighborhood
