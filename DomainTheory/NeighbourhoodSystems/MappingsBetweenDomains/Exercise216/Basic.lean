/-ai
This file gathers and re-exports the approximable-map infrastructure, the neighbourhood domain of binary strings, the parity map into the flat truth-value domain, the three parity equations, and the prefixing map. Prefixing a finite string is approximable by the relation that asks the prefixed input neighbourhood to be contained in the output neighbourhood, and its elementwise action is Scott's prefixing operation. Among approximable maps, the parity map is the unique solution of the equations that a leading one yields true, a leading zero followed by one yields false, and a leading pair of zeros reproduces the value on the remaining string.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise216.SatisfiesParityEquations
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise216.sigmaMap

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

namespace DomainTheory.NeighbourhoodSystems.Exercise216

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-! ## Exercise 2.16, second half — the parity map is *uniquely* determined by its equations -/

end DomainTheory.NeighbourhoodSystems.Exercise216
