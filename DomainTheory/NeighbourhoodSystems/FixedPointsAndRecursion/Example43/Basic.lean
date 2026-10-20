module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.memN
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.natElem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.zeroElt
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.constLiftN
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.succMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.predVal
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.predMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.zeroVal
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.zeroMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.memN_univ
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.memN_singleton
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.univ_ne_singleton
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.singleton_ne_univ
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.singleton_nat_inj
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.nestedOrDisjoint
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.N
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.N_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.N_master
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.T

@[expose] public section

/-!
# Example 4.3 (Scott 1981, PRG-19, §4) — the natural-number domain `N`

Scott's "THE domain of integers" (pages 57–61). The tokens are `ℕ`, and the neighbourhoods are

`N = {{n} ∣ n ∈ ℕ} ∪ {ℕ}`

— a *flat* domain: the singletons `{n}` are the finite total elements and the whole space `ℕ`
is the least-informative neighbourhood `Δ = ⊥`. We build `N` by the nested-or-disjoint criterion
(`ofNestedOrDisjoint`): any two neighbourhoods are nested (one is `ℕ`) or disjoint (distinct
singletons).

The (ideal) elements of `|N|` are exactly: the bottom `⊥ = {ℕ}` ("undefined"), and for each `n`
the total element `n̂ = ↑{n} = {{n}, ℕ}` (`natElem n`). Scott then equips `N` with the structure
maps

* `succ, pred : N → N`     (`succMap`, `predMap`)
* `zero : N → T`           (`zeroMap`, into the truth domain `T` of Example 1.2),

making `⟨N, 0, succ, pred, zero⟩` "THE domain of integers". All three are *strict* approximable
maps determined by their action on the finite total elements:

* `succ(n̂) = (n+1)^`,            `succ(⊥) = ⊥`;
* `pred((n+1)^) = n̂`, `pred(0̂) = ⊥`, `pred(⊥) = ⊥`;
* `zero(0̂) = true`, `zero((n+1)^) = false`, `zero(⊥) = ⊥`.

We capture the common shape — a map `N → V` sending `n̂ ↦ val n` and `⊥ ↦ ⊥` — once and for all in
the combinator `constLiftN`, whose computation rules `constLiftN_natElem`/`constLiftN_bot` give all
of the displayed equations uniformly. The data (`N`, `constLiftN`, `succMap`, `predMap`) is
**choice-free** (`#print axioms ⊆ {propext, Quot.sound}`); `zeroMap` inherits `Classical.choice`
structurally from the truth domain `T` of Example 1.2 exactly as `Example23.parityMap` does.
-/

namespace DomainTheory.NeighbourhoodSystems.Example43

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

/-! ### The neighbourhood system `N`. -/











/-! ### The total elements `n̂`. -/



/-! ### The strict lifting combinator `n̂ ↦ val n`, `⊥ ↦ ⊥`. -/


/-! ### The successor map `succ : N → N`. -/


/-! ### The predecessor map `pred : N → N`. -/



/-! ### The test map `zero : N → T`. -/




/-! ### `pred` undoes `succ`. -/
end DomainTheory.NeighbourhoodSystems.Example43
