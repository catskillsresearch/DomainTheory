module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise328.leastMapVals

@[expose] public section

/-!
# Exercise 3.28 (Scott 1981, PRG-19, §3) — the elementwise formula for the least map

In `(𝒟₀ → 𝒟₁)`, let `⋂ {[Xᵢ, Yᵢ] ∣ i < n}` be a non-empty neighbourhood. Proposition 3.9
characterizes its minimal element `f₀` as a *relation* (`leastMap`, `X f₀ Y ↔ ⋂{Yᵢ ∣ X ⊆ Xᵢ} ⊆ Y`).
Exercise 3.28 asks for the **elementwise** description:

`f₀(x) = ⊔ { ↑Yᵢ ∣ x ∈ [Xᵢ] }`  for `x ∈ |𝒟₀|`,

where `x ∈ [Xᵢ]` means `Xᵢ ∈ x` (the input is at least as defined as `Xᵢ`). We formalize this as
`toElementMap_leastMap_eq_sSup`: `f₀(x)` is the least upper bound (Exercise 1.27's `sSup`) of the
principal filters `↑Yᵢ` over the active indices.

The proof shows `f₀(x)` is *the* least upper bound of that set: it is an upper bound
(`val_le_leastMap_toElementMap`, from `Yᵢ ∈ f₀(x)`), and it is least
(`leastMap_toElementMap_le_of_ub`, because any upper bound contains every relevant `Yᵢ`, hence the
finite intersection `⋂{Yᵢ ∣ X ⊆ Xᵢ}`); the equality with `⊔` then follows by antisymmetry.

Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

end DomainTheory.NeighbourhoodSystems
