/-ai
This file gathers and re-exports Scott's sum of two neighbourhood systems: the left and right tags, the tagged copies and their membership, intersection, nonemptiness, inclusion, and disjointness lemmas, the sum master and the sum system, the left and right contents of a sum set, and the injections and projections together with the identities in which each projection retracts the corresponding injection.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.il
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.ir
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.sumMaster
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.leftPart
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.rightPart
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.inMap₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.inMap₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.outMap₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.outMap₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.il_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.ir_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.none_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.ir_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.il_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.none_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.inj₀_inter
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.inj₁_inter
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.inj₀_inter_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.inj₀_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.inj₁_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.inj₀_subset_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.inj₁_subset_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.none_mem_sumMaster
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.inj₀_subset_sumMaster
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.inj₁_subset_sumMaster
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.sumMaster_inter_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.sumMaster_inter_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.il_injective
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.ir_injective
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.il_preimage_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.ir_preimage_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.mem_leftPart
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.mem_rightPart
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.leftPart_mono
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.rightPart_mono
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.leftPart_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.rightPart_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.leftPart_sumMaster
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.leftPart_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.rightPart_sumMaster
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.rightPart_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.leftPart_mem
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.rightPart_mem

@[expose] public section

/-!
# Exercise 3.18 (Scott 1981, PRG-19, §3) — the sum (coproduct) system

Scott's sum of `𝒟₀` (over `Δ₀`) and `𝒟₁` (over `Δ₁`), assuming *no neighbourhood is empty*:

`𝒟₀ + 𝒟₁ = {{Λ} ∪ 0Δ₀ ∪ 1Δ₁} ∪ {0X ∣ X ∈ 𝒟₀} ∪ {1Y ∣ Y ∈ 𝒟₁}`,

a neighbourhood system over `{Λ} ∪ 0Δ₀ ∪ 1Δ₁`. We model the tokens as `Option (α ⊕ β)`: `Λ = none`,
`0a = some (inl a)`, `1b = some (inr b)`; then `0X = il '' X` and `1Y = ir '' Y`.

The non-emptiness assumption (`h₀`, `h₁`) is exactly what makes the system closed under intersection:
the two tagged copies are disjoint (`inj₀ X ∩ inj₁ Y = ∅`), so a cross pair `0X, 1Y` is *inconsistent*
(no non-empty neighbourhood lies in `∅`), and same-tag intersections reduce to those of the factors.

We then build the injections `inMapᵢ : 𝒟ᵢ → 𝒟₀ + 𝒟₁` and projections `outMapᵢ : 𝒟₀ + 𝒟₁ → 𝒟ᵢ`,
and prove `outMapᵢ ∘ inMapᵢ = I_{𝒟ᵢ}`. (The non-emptiness assumption is what makes the system a
neighbourhood system; the section/retraction identities hold for the resulting maps.)

Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}


variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)


variable {V₀ V₁}


/-! ### The injections `inᵢ` and projections `outᵢ`. -/


variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}


end DomainTheory.NeighbourhoodSystems
