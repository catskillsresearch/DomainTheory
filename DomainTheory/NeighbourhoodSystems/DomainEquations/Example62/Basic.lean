/-ai
This file gathers and re-exports the bit tagging of sets of binary strings, the two directions of the correspondence between the binary-sequence domain and the sum of that domain with itself, and the lemmas on cones, intersections, injectivity, and neighbourhood shapes used to prove that the two domains are isomorphic.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.toBB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.fromBB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.bbEquiv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.mem_embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.embBit_eq_prepend
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.embBit_cone
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.memB_embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.nil_not_mem_embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.embBit_ne_univ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.embBit_inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.embBit_inter_ne
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.embBit_subset
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.embBit_injective
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.memB_embBit_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.embBit_ne
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.B_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.memB_cases
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.BB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.sum_mem_inj₀_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.sum_mem_inj₁_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.sum_mem_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.toBB_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.toBB_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.fromBB_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.fromBB_mem_embT
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.fromBB_toBB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.toBB_fromBB

@[expose] public section

/-!
# Example 6.2 (Scott 1981, PRG-19, §6) — `B` and `C` as solutions of domain equations

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19 (1981), Lecture VI,
*Introduction to domain equations*. Scott observes that the staple examples `B` (binary sequences,
Example 1.B) and `C` (finite-or-infinite binary sequences, Example 4.4) satisfy *domain equations*:

`B ≅ B + B`,    `C ≅ {{Λ}} + C + C`,

where, "if we liked", both systems can be presented over `{0,1}*` as the least families

`B = {Σ*} ∪ {0X ∣ X ∈ B} ∪ {1X ∣ X ∈ B}`,
`C = {Σ*} ∪ {{Λ}} ∪ {0X ∣ X ∈ C} ∪ {1X ∣ X ∈ C}`.

This module formalizes the **`B ≅ B + B`** half. (See `Example62C.lean` for `C`'s three-way
equation `C ≅ 𝟙 + C + C`.)

The point of the equation is that a neighbourhood of `B` is either the master `Σ*` (`= cone []`), a
`0`-prefixed copy `0X` (`= embBit false X`), or a `1`-prefixed copy `1X` (`= embBit true X`) — exactly
the three shapes that build the sum `B + B` (Exercise 3.18): the fresh basepoint, the left copy `0X`,
and the right copy `1Y`. We exhibit the order-isomorphism `bbEquiv : |B| ≃o |B + B|` directly from the
filter maps `toBB` (forward) / `fromBB` (inverse), mirroring `Example61.dsharpEquiv`.

All *data* is choice-free (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

/-! ### Prepending a single bit: `bX = {bw' ∣ w' ∈ X}`. -/


/-! ### `B` is positive (no empty neighbourhood) and its neighbourhood-shape classification. -/


/-! ### The sum target `B + B` and its inversion lemmas. -/


/-! ### The forward half `toBB : |B| → |B + B|`. -/


/-! ### The inverse half `fromBB : |B + B| → |B|`. -/


/-! ### The two halves are mutually inverse. -/


/-! ### The domain equation `B ≅ B + B`. -/

end Example62
end DomainTheory.NeighbourhoodSystems
