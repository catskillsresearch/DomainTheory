/-ai
This file gathers and re-exports the tails and their membership, the shift and its monotonicity and tail and singleton laws, the unary neighbourhood predicate and its closure and universe laws, the nesting lemmas, the neighbourhood system and its membership and master, the partial and total elements, the successor map, the infinite element, and the map from the flat naturals. The module comment records Scott's unary analogue of the sequence domain: neighbourhoods are tails and singletons, total elements are finite strings of ones, partial elements are tails, the successor prepends a one and has an infinite fixed point, and the flat naturals map into this domain by sending a numeral to the corresponding finite string and bottom to bottom.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.tail
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.shift
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.memC1
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.C1
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.oneBot
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.oneElem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.consMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.infElt
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.relateNToC1
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.tail_zero
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.mem_tail
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.shift_tail
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.shift_singleton
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.shift_mono
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.memC1_tail
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.memC1_singleton
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.memC1_univ
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.memC1_shift
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.singleton_tail_nd
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.nestedOrDisjoint
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.C1_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.C1_master

@[expose] public section

/-!
# Exercise 4.25 (Scott 1981, PRG-19, Lecture IV) — the unary sequence domain `C₁`

*"Perhaps the domains `N` and `C` are not exactly analogous?"* `C` (Example 4.4) was built over the
two-letter alphabet `{0,1}`. Scott asks to build the analogue `C₁` over `{1}*` — finite strings of
`1`s, which we encode by their length `n ∈ ℕ` (so `1ⁿ ↔ n`). The neighbourhoods are the **tails**
and the **singletons**:

`C₁ = {{1ᵐ ∣ m ≥ n} ∣ n ∈ ℕ} ∪ {{1ⁿ} ∣ n ∈ ℕ}`     (`tail n = {m ∣ n ≤ m}`, `{n}`).

This is again a nested-or-disjoint system (`ofNestedOrDisjoint`): the tails form a descending chain
and a singleton is either inside a tail or disjoint from it. The total elements are the finite
strings `1ⁿ` (`oneElem n = ↑{n}`) and the partial elements `1ⁿ⊥` ("at least `n` ones",
`oneBot n = ↑(tail n)`).

The structure **analogous to `C`** is the single successor `x ↦ 1x` (`consMap`, prepending a `1`,
i.e. shifting the length up by one), with `consMap_oneElem`/`consMap_oneBot`. Crucially — and this is
Scott's point that `N` and `C` are *not* analogous — `C₁` is **not flat** like `N`: the successor has
a genuine *infinite* fixed point `1^∞ = 1·1^∞` (`infElt`, `infElt_eq`), the limit `⊔ₙ 1ⁿ⊥` of the
tails, which has no counterpart among the elements `⊥, 0̂, 1̂, 2̂, …` of the flat domain `N`. So `C₁`
is the genuine unary analogue of `C` (`= C₂`), distinct from `N`.

Finally, the systems are **related by approximable maps**: e.g. `relateNToC1 : N → C₁` sends the
numeral `n̂` to the finite string `1ⁿ` and is strict (`⊥ ↦ ⊥`) — the natural "length ↦ unary
expansion" map (`relateNToC1_natElem`, `relateNToC1_bot`).

The data (`C₁`, `consMap`, `relateNToC1`) is **choice-free** (`#print axioms ⊆ {propext,
Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems.Exercise425

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

/-! ### Tails, singletons, and the shift. -/


/-! ### The neighbourhood system `C₁`. -/


/-! ### Elements: `1ⁿ` (total) and `1ⁿ⊥` (partial). -/


/-! ### The successor `x ↦ 1x`. -/


/-! ### The infinite element `1^∞ = 1·1^∞`. -/


/-! ### An approximable map relating `N` and `C₁`. -/

end DomainTheory.NeighbourhoodSystems.Exercise425
