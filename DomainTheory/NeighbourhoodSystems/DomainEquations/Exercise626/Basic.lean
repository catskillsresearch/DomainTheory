/-ai
This file gathers and re-exports the lifting of Exercise 6.26: the lift master and the lifted neighbourhood system, the lift of a Scott system, the fresh bottom and the lifted elements with their inverse, the action on approximable maps, and the comparison maps between the coalesced sum of lifts and the separated sum and between the smash of lifts and the lift of the product, together with the membership and round-trip lemmas those comparisons use.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.liftTokMaster
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.liftTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.lift
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.liftBot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.liftUp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.unlift
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.liftMapTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.toSumLift
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.fromSumLift
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.sumLiftEquiv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.toLiftProd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.fromLiftProd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.liftProdEquiv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.nil_mem_liftTokMaster
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.embF_subset_liftTokMaster
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.liftTokMaster_inter_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.embF_ne_liftTokMaster
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.liftTok_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.liftTok_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.liftTok_mem_embF_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.mem_liftBot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.mem_liftUp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.o_mem_embFF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.o_mem_embTF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.o_embFF_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.o_embTF_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.toSumLift_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.toSumLift_mem_embT
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.fromSumLift_mem_embFF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.fromSumLift_mem_embTF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.fromSumLift_toSumLift
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.toSumLift_fromSumLift
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.ot_mem_prod
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.ot_mem_prod_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.lp_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.lp_prod_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.toLiftProd_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.fromLiftProd_mem_prod
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.fromLiftProd_toLiftProd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.toLiftProd_fromLiftProd

@[expose] public section

/-!
# Exercise 6.26 (Scott 1981, PRG-19, §6) — the lifting `𝒟_⊥` over `{0,1}*`

> **EXERCISE 6.26.** For systems `𝒟` as in 6.19 define
> `𝒟_⊥ = {{Λ} ∪ 0Δ} ∪ {0X ∣ X ∈ 𝒟}`.
> Describe the construct in terms of elements. Is this a suitable functor? Prove that
> `𝒟_⊥ ⊕ ℰ_⊥ ≅ 𝒟 + ℰ`. What is `𝒟_⊥ ⊗ ℰ_⊥ ≅ ??`

The **lifting** `𝒟_⊥` adds a *new bottom* below a `0`-tagged copy of `𝒟`. Its master is
`{Λ} ∪ 0Δ` and its proper neighbourhoods are the `0X` for `X ∈ 𝒟` (including `0Δ`, which sits
strictly above the new bottom `{{Λ} ∪ 0Δ}`). It is the one-summand analogue of Exercise 6.19's sum.

## Contents

* `liftTok`/`ScottSys.lift` — the lifted system over `Str = {0,1}*`, again `∅`-free.
* **Elements** (`liftBot`, `liftUp`, `unlift`): `|𝒟_⊥| ≅ |𝒟|_⊥`. The bottom `liftBot` is the fresh
  least element; `liftUp x` embeds `|𝒟|` order-isomorphically *above* it (`liftBot_lt_liftUp`,
  `liftUp_le_liftUp_iff`); every element is one or the other (`eq_liftBot_or_exists_liftUp`).
* **Functor** (`liftMapTok`, `liftMapTok_isStrict`, `liftMapTok_id`, `liftMapTok_comp`): *yes*, `(·)_⊥`
  is a (strict) functor on Scott's category — the action on maps preserves identities and composition.
* **`𝒟_⊥ ⊕ ℰ_⊥ ≅ᴰ 𝒟 + ℰ`** (`lift_oplus_lift_iso_sum`): coalescing the two fresh bottoms of the
  lifts reproduces exactly the separated sum.
* **`𝒟_⊥ ⊗ ℰ_⊥ ≅ᴰ (𝒟 × ℰ)_⊥`** (`lift_otimes_lift_iso_lift_prod`): the answer to Scott's `??` — the
  smash of two lifts is the lift of the product.

All constructions are **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`); the lone exception
is `eq_liftBot_or_exists_liftUp`, a `Prop`-level case split that uses excluded middle (`Classical`)
to decide whether an element lies above the fresh bottom — unavoidable and called out there.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D : NeighborhoodSystem Str}

/-! ## The lifted system `𝒟_⊥` over `{0,1}*` -/









variable {hD : ∀ X, D.mem X → X.Nonempty}



/-! ## Elements: `|𝒟_⊥| ≅ |𝒟|_⊥` -/






/-! ## Functoriality: `(·)_⊥` is a strict functor -/

variable {A B C : ScottSys}


/-! ## `𝒟_⊥ ⊕ ℰ_⊥ ≅ᴰ 𝒟 + ℰ`

The coalesced sum of the two lifts has tokens `0·0·X'` (`X' ∈ 𝒟`) and `1·0·Y'` (`Y' ∈ ℰ`), with the
shared bottom `{Λ} ∪ 0(liftTokMaster 𝒟) ∪ 1(liftTokMaster ℰ)`. The separated sum `𝒟 + ℰ` has tokens
`0X'`, `1Y'`. The element iso simply *deletes the inner `0`*. The cross-tag intersections vanish
(`∅`-freeness), exactly as in Exercise 6.19's `toSum`/`fromSum`. -/

variable {D E : ScottSys}














/-! ## `𝒟_⊥ ⊗ ℰ_⊥ ≅ᴰ (𝒟 × ℰ)_⊥` — the answer to Scott's `??`

The smash of the two lifts has proper neighbourhoods `{Λ} ∪ 0(0X') ∪ 1(0Y')` (i.e.
`prodTokNbhd (0X') (0Y')`, with `X' ∈ 𝒟`, `Y' ∈ ℰ`). The lift of the product has proper
neighbourhoods `0(prodTokNbhd X' Y')`. The element iso transports one rectangle presentation to the
other. Unlike the sum there are *no* cross-tag intersections, so the proof is purely "rectangular". -/











end Exercise619
end DomainTheory.NeighbourhoodSystems
