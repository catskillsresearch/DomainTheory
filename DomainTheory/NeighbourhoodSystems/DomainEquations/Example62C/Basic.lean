/-ai
This file gathers and re-exports the development of Scott's equation C ≅ {{Λ}} + C + C: the three-way separated sum and its master, the tagged copies, the maps toCC and fromCC, and the order isomorphism ccEquiv, together with the lemmas that support them.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.master3
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.sum3
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.toCC
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.fromCC
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.ccEquiv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t0_mem_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t1_mem_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t2_mem_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.none_not_mem_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.none_not_mem_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.none_not_mem_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t1_not_mem_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t2_not_mem_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t0_not_mem_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t2_not_mem_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t0_not_mem_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t1_not_mem_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j0_inter_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j1_inter_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j2_inter_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j0_inter_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j0_inter_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j1_inter_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j0_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j1_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j2_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j0_subset_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j1_subset_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j2_subset_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j1_injective
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j2_injective
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.none_mem_master3
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j0_subset_master3
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j1_subset_master3
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j2_subset_master3
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.master3_inter_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.master3_inter_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.master3_inter_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.eq_master3_of_subset
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.unitSys_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.C_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.embBit_singleton
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.memC_embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.memC_cases
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.memC_embBit_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.singleton_nil_inter_embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.singleton_nil_ne_univ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.singleton_nil_ne_embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.CC
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.sum3_mem_j1_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.sum3_mem_j2_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.sum3_mem_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.toCC_mem_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.toCC_mem_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.toCC_mem_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.fromCC_mem_nil
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.fromCC_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.fromCC_mem_embT
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.fromCC_toCC
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.toCC_fromCC

@[expose] public section

/-!
# Example 6.2 (Scott 1981, PRG-19, §6) — `C ≅ {{Λ}} + C + C`

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19 (1981), Lecture VI.
This module formalizes the second domain equation of Example 6.2, for the system `C` of finite or
infinite binary sequences (Example 4.4):

`C ≅ {{Λ}} + C + C`,

where `{{Λ}} = 𝟙` is the one-point (unit) domain (Exercise 3.15). Presented over `{0,1}*`,

`C = {Σ*} ∪ {{Λ}} ∪ {0X ∣ X ∈ C} ∪ {1X ∣ X ∈ C}`,

so a neighbourhood of `C` is the master `Σ*` (`= cone []`), the terminator `{Λ} = {[]}`, a `0`-copy
`0X = embBit false X`, or a `1`-copy `1X = embBit true X`. These four shapes are exactly those of a
**three-way separated sum** `𝟙 + C + C`: a fresh basepoint, plus one `𝟙`-copy (the lone `{Λ}`), plus
two `C`-copies.

Crucially this is a genuine *three-way* sum: nesting the binary sum (`𝟙 + (C + C)`) would introduce a
spurious extra bottom element (the inner sum's basepoint) with no counterpart in `C`. So we first build
the three-way separated sum `sum3` (mirroring Exercise 3.18), then exhibit the order-isomorphism
`ccEquiv : |C| ≃o |𝟙 + C + C|`.

All *data* is choice-free (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

/-! ## The three-way separated sum `D₀ + D₁ + D₂`.

Tokens are `Option (α ⊕ β ⊕ γ)`: a fresh basepoint `Λ = none` below three disjoint tagged copies. -/







variable {α β γ : Type*}



























variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)


variable {V₀ V₁ V₂}










/-! ## The domain equation `C ≅ 𝟙 + C + C`. -/

namespace Example62C














/-! ### The forward half `toCC : |C| → |𝟙 + C + C|`. -/





/-! ### The inverse half `fromCC : |𝟙 + C + C| → |C|`. -/





/-! ### The two halves are mutually inverse. -/



/-! ### The domain equation `C ≅ 𝟙 + C + C`. -/

end Example62C
end DomainTheory.NeighbourhoodSystems
