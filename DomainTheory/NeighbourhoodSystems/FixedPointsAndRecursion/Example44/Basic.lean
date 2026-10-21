/-ai
This file gathers and re-exports the domain of finite and infinite binary sequences: the neighbourhood predicate, cones and singletons and their comparisons, monotonicity of prepending and its action on singletons, closure of neighbourhoods under prepending, the system with its membership and master, the partial and total elements, the maps that prepend a bit, and the alternating fixed-point element.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.memC
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.strBot
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.strElem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.consMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.altElt
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.prepend_singleton
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.prepend_mono
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.memC_cone
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.memC_singleton
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.singleton_subset_cone
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.singleton_cone_nd
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.nestedOrDisjoint
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.C
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.C_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.C_master
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.memC_prepend

@[expose] public section

/-!
# Example 4.4 (Scott 1981, PRG-19, §4) — the domain `C` of binary sequences

Scott's domain `C` of *finite or infinite binary sequences* (pages 61–64), a generalization of the
natural-number domain `N` of Example 4.3. Over the tokens `Σ* = List Bool` (Scott's `Σ = {0,1}`,
`Λ = []`), recall the cones `cone σ = σΣ*` of Example 1.B. The system `C` adds the *singletons*:

`C = {σΣ* ∣ σ ∈ Σ*} ∪ {{σ} ∣ σ ∈ Σ*}`.

The total elements correspond to finite or infinite sequences: `σ = ↑{σ}` (`strElem σ`, the finite
sequence `σ` *completed*) and `σ⊥ = ↑σΣ*` (`strBot σ`, the partial element "starts with `σ`"). `C`
is again nested-or-disjoint, so it is a neighbourhood system (`ofNestedOrDisjoint`).

We equip `C` with the two **successors** `x ↦ 0x` and `x ↦ 1x` (`consMap false`, `consMap true`),
prepending a bit, with their action on the finite/partial elements (`consMap_strElem`,
`consMap_strBot`). As Scott's illustration that recursion now lives inside `|C|`, we then define the
alternating sequence `a = 01a` as the least fixed point of `x ↦ 0(1x)` (`altElt`, `altElt_eq`),
using the Fixed-point Theorem 4.1.

The remaining structure maps Scott lists for `⟨C, Λ, 0, 1, tail, empty, zero, one⟩` — the
predecessor analogue `tail` (`tail(0x) = tail(1x) = x`, `tail(Λ) = ⊥`) and the three tests
`empty, zero, one : C → T` — are exactly the parts Scott leaves as exercises ("It is left to the
reader to show that **tail** exists as an approximable mapping"; "it is an exercise to show these
are approximable", Exercise 4.19); they are out of scope for this module.

The data constructions (`C`, `consMap`) are **choice-free** (`#print axioms ⊆ {propext,
Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems.Example44

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB

/-! ### Prepending a bit: set-level lemmas (reused from Example 1.B). -/


/-! ### The neighbourhood system `C`. -/


/-! ### Elements of `C`: `σ` (total) and `σ⊥` (partial). -/


/-! ### The successor maps `x ↦ bx`. -/


/-! ### A fixed-point element: the alternating sequence `a = 01a`. -/

end DomainTheory.NeighbourhoodSystems.Example44
