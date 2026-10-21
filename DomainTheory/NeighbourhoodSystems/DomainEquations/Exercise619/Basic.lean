/-ai
This file gathers and re-exports the token-level sum and product of Exercise 6.19 on strings. It re-exports the concrete sum and its master, the maps to and from the abstract sum and the equivalence they determine, the concrete product and its neighbourhoods, the component maps and the pairing and their equivalence with the abstract product, and the membership, intersection, subset, injectivity, splitting, and inversion lemmas used to construct them.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sumTokMaster
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sumTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.toSum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.fromSum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sumTokEquiv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.prodTokNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.prodTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.fstTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sndTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.pairTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.prodTokEquiv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.nil_mem_sumTokMaster
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.embF_subset_sumTokMaster
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.embT_subset_sumTokMaster
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sumTokMaster_inter_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sumTokMaster_inter_embT
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.embF_ne_sumTokMaster
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.embT_ne_sumTokMaster
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sumTok_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sumTok_mem_embT
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sumTok_mem_embF_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sumTok_mem_embT_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sumTok_mem_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sum_mem_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sum_mem_inj₀_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sum_mem_inj₁_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.toSum_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.toSum_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.fromSum_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.fromSum_mem_embT
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.fromSum_toSum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.toSum_fromSum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.mem_prodTokNbhd_nil
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.mem_prodTokNbhd_false
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.mem_prodTokNbhd_true
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.prodTokNbhd_inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.prodTokNbhd_subset_iff
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.prodTokNbhd_injective
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.prodTok_mem_iff
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.prodTok_mem_prodTokNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.prodTok_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.mem_fstTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.mem_sndTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.prodTok_mem_split
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.mem_pairTok_prodTokNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.pairTok_fstTok_sndTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.fstTok_pairTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sndTok_pairTok

@[expose] public section

/-!
# Exercise 6.19 (Scott 1981, PRG-19, §6) — sum and product on the category of strict maps

> **EXERCISE 6.19.** For the sake of uniformity restrict attention to systems `𝒟` on sets
> `Δ ⊆ {0,1}*`, where `Λ ∈ Δ` and `∅ ∉ 𝒟`, and to the category of strict maps. Define sum and
> product by
> `𝒟₀ + 𝒟₁ = {{Λ} ∪ 0Δ₀ ∪ 1Δ₁} ∪ {0X ∣ X ∈ 𝒟₀} ∪ {1Y ∣ Y ∈ 𝒟₁}`,
> `𝒟₀ × 𝒟₁ = {{Λ} ∪ 0X ∪ 1Y ∣ X ∈ 𝒟₀ and Y ∈ 𝒟₁}`.
> Are these correct up to isomorphism? …

This module formalizes **Part A** of the exercise: Scott's *uniform* token-level presentations of
sum and product over `{0,1}*` (so that the constructions are genuine *endo*-operations on a single
category, unlike the abstract separated sum `𝒟₀ + 𝒟₁` of Exercise 3.18 over `Option (α ⊕ β)` or the
product `𝒟₀ × 𝒟₁` of Definition 3.1 over `α ⊕ β`), and the answer to *"Are these correct up to
isomorphism?"* — **yes**:

* `sumTok_iso_sum : sumTok D₀ D₁ h₀ h₁ ≅ᴰ sum D₀ D₁ h₀ h₁`, and
* `prodTok_iso_prod : prodTok D₀ D₁ ≅ᴰ prod D₀ D₁`.

We reuse the single-bit prefix `embBit b X = bX` of Example 6.2 (so `0X = embBit false X`,
`1Y = embBit true Y`), whose disjointness/intersection algebra (`embBit_inter`, `embBit_inter_ne`,
`embBit_subset`, `embBit_injective`, `embBit_nonempty`) is exactly what makes the concrete sum a
neighbourhood system and drives the isomorphism (a token-level analogue of `Example62.bbEquiv`,
generalised from `B` to arbitrary `∅`-free `D₀, D₁`).

The functor-algebra closure (all `T(X)` generated by constants/identity/sum/product are functors,
continuous on maps, monotone and continuous on domains) is **Part B**, deferred.

Everything here is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example62 ExampleB

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

/-! ## The concrete sum `D₀ + D₁` over `{0,1}*`

`D₀ + D₁ = {{Λ} ∪ 0Δ₀ ∪ 1Δ₁} ∪ {0X ∣ X ∈ 𝒟₀} ∪ {1Y ∣ Y ∈ 𝒟₁}`, with `Λ = []`, `0X = embBit false X`,
`1Y = embBit true Y`. -/










variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}






/-! ### Generic inversion lemmas for the abstract separated sum `sum D₀ D₁` -/




/-! ### The forward half `toSum : |D₀ + D₁|ₜₒₖ → |D₀ + D₁|` -/




/-! ### The inverse half `fromSum : |D₀ + D₁| → |D₀ + D₁|ₜₒₖ` -/




/-! ### The two halves are mutually inverse, giving the isomorphism. -/




/-! ## The concrete product `D₀ × D₁` over `{0,1}*`

`D₀ × D₁ = {{Λ} ∪ 0X ∪ 1Y ∣ X ∈ 𝒟₀ and Y ∈ 𝒟₁}`. Every neighbourhood carries *both* coordinates and
the basepoint, in contrast to the sum (where a proper neighbourhood refines exactly one summand). -/












/-! ### Components of a product element and the splitting lemma -/






/-! ### The element pairing and the isomorphism `|D₀ × D₁|ₜₒₖ ≃o |D₀| × |D₁|`. -/






end Exercise619
end DomainTheory.NeighbourhoodSystems
