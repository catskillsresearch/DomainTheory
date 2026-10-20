/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Approximable
public import DomainTheory.Neighborhood.ExampleB
public import DomainTheory.Neighborhood.Example23

@[expose] public section

/-!
# Exercise 2.16 (Scott 1981, PRG-19, §2) — the prefixing map `x ↦ σx` is approximable

In Lecture I (Example 1.B) Scott defined, for each finite string `σ ∈ Σ*`, the elementwise operation
`x ↦ σx` on `|B|` (`ExampleB.sigmaElt`). Exercise 2.16 asks whether this mapping is *approximable*.
It is: the witnessing neighbourhood relation is

`X f Y ↔ X, Y ∈ B ∧ σX ⊆ Y`,

i.e. "the prefixed input cone `σX` is at least as sharp as `Y`." We package it as
`sigmaMap σ : ApproximableMap B B` and show its elementwise action is exactly `sigmaElt σ`
(`toElementMap_sigmaMap`).

**Second half.** Scott also asks to show that the parity map `f : B → T` of Example 2.3
(`Example23.parityMap`) is *uniquely* determined among approximable mappings by the three
equations `f(1x)=true`, `f(01x)=false`, `f(00x)=f(x)` (`SatisfiesParityEquations`). We check
`parityMap` itself satisfies them (`Example23.parityMap_toElementMap_sigmaElt`, so the statement
is non-vacuous) and then prove uniqueness (`eq_parityMap_of_satisfies`): the recursive core
(`key`) pins down any such `g` on every principal element `σ⊥`, peeling two tokens of `σ` at a
time (mirroring `scan`'s own recursion); the base case `σ = []` and the leftover singleton
`σ = [false]` are the two places genuine order theory (flatness of `𝒯`, `Example23.eq_botElt_of_le`)
enters, everything else being pure substitution into the equations.

Constructive except for the `by_cases` in `ApproximableMap.ext`'s use of `Classical.em`
(`#print axioms ⊆ {propext, Classical.choice, Quot.sound}`). -/

namespace DomainTheory.Neighborhood.Exercise216

open DomainTheory.Neighborhood NeighborhoodSystem ExampleB

/-- **Exercise 2.16 — `x ↦ σx` is approximable.** The neighbourhood relation `X f Y ↔ σX ⊆ Y`
(confined to `B × B`). Definition 2.1: (i) `σΔ ⊆ Δ`; (ii) the prefixed cone `σX` is a common lower
bound of `Y, Y'`, witnessing `Y ∩ Y' ∈ B`; (iii) `prepend_mono` shrinks `σX'` as `X' ⊆ X`. -/
def sigmaMap (σ : Str) : ApproximableMap B B where
  rel X Y := B.mem X ∧ B.mem Y ∧ prepend σ X ⊆ Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨B.master_mem, B.master_mem, Set.subset_univ _⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY, hsub⟩ ⟨_, hY', hsub'⟩
    have hpre : B.mem (prepend σ X) := memB_prepend σ hX
    have hsubInter : prepend σ X ⊆ Y ∩ Y' := Set.subset_inter hsub hsub'
    exact ⟨hX, B.inter_mem hY hY' hpre hsubInter, hsubInter⟩
  mono := by
    rintro X X' Y Y' ⟨_, _, hsub⟩ hX'X hYY' hX' hY'
    exact ⟨hX', hY', ((prepend_mono σ hX'X).trans hsub).trans hYY'⟩

/-! ## Exercise 2.16, second half — the parity map is *uniquely* determined by its equations -/

/-- **The three equations of Exercise 2.16.** `f(1x) = true`, `f(01x) = false`, `f(00x) = f(x)`,
for *every* `x : |B|`. -/
structure SatisfiesParityEquations (g : ApproximableMap B Example23.T) : Prop where
  one : ∀ x : B.Element, g.toElementMap (sigmaElt [true] x) = Example23.trueElt
  zeroOne : ∀ x : B.Element, g.toElementMap (sigmaElt [false, true] x) = Example23.falseElt
  zeroZero : ∀ x : B.Element, g.toElementMap (sigmaElt [false, false] x) = g.toElementMap x
end DomainTheory.Neighborhood.Exercise216
