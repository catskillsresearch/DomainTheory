/-ai
This file gathers and re-exports the initial-algebra half of Exercise 6.18. It re-exports the cons isomorphism of the infinite iterate with its product, the descent sequence and the descent map, the strictness of that map and the homomorphism it determines, the truncation chain and the theorem that its supremum is the identity, the uniqueness of a strict homomorphism, and the initiality of the infinite iterate for the product functor on empty-free domains, together with the supporting lemmas on bottoms, monotonicity, and chains.

The product of two strict approximable maps is strict.

The numbered name example_618 is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.isStrict_prodMap

@[expose] public section

/-!
# Exercise 6.18 (Scott 1981, PRG-19, §6) — `𝒟^∞` as an initial algebra

> **EXERCISE 6.18.** With reference back to Exercise 3.16 discuss the construction of `𝒟^∞` as an
> initial algebra and as a solution to the domain equation `𝒟^∞ ≅ 𝒟 × 𝒟^∞`.

Exercise 3.16 already constructs the infinite iterate `𝒟^∞` (`iterSys`, over `ℕ × Δ`) and proves the
**domain-equation** half, `𝒟^∞ ≅ 𝒟 × 𝒟^∞` (`iter_isomorphic`, with the explicit element iso
`iterProdIso`). This module supplies the **initial-algebra** half.

For a fixed `∅`-free domain `𝒟` consider the (product) endofunctor
`T(X) = 𝒟 × X`. The domain equation `𝒟^∞ ≅ T(𝒟^∞)` makes `𝒟^∞` a `T`-algebra, with structure map
`i : 𝒟 × 𝒟^∞ → 𝒟^∞` the "cons" isomorphism (Exercise 3.16's `iterProdIso⁻¹`). We prove **`𝒟^∞` is the
initial `T`-algebra**: for every `T`-algebra `(E, k)` there is a *unique* (strict) homomorphism
`𝒟^∞ → E`, namely `h(⟨x₀,x₁,…⟩) = k(x₀, k(x₁, k(x₂, …)))`, the least fixed point of
`λh. k ∘ T(h) ∘ j`.

## Architecture

The genuine analysis is done at the level of plain approximable maps (over `iterSys V`,
`prod V (iterSys V)`, and a target `E`), then packaged into the bespoke category `StrictDomainObj`
of `∅`-free domains and strict maps (Exercise 6.17), where `IsInitial` directly expresses Scott's
universal property among strict algebras (cf. Theorem 6.14, which is initiality *among strict
algebras* — the product functor grows the token set, so Theorem 6.14's same-carrier colimit tower
does **not** apply, and `𝒟^∞` must be built directly as in Exercise 3.16).

* **Existence.** `descMap = ⋃ₙ hₙ`, `h₀ = ⊥`, `hₙ₊₁ = k ∘ T(hₙ) ∘ j`. It is strict and satisfies the
  fixed-point equation `descMap = k ∘ T(descMap) ∘ j`, hence the homomorphism square
  `descMap ∘ i = k ∘ T(descMap)` (since `j ∘ i = I`).
* **Uniqueness.** The truncation chain `ρₙ : 𝒟^∞ → 𝒟^∞`, `ρ₀ = ⊥`, `ρₙ₊₁ = i ∘ T(ρₙ) ∘ j`,
  computes to `ρₙ(⟨xᵢ⟩) = ⟨x₀,…,x_{n-1},⊥,⊥,…⟩` (`rho_apply`) and satisfies `⋃ₙ ρₙ = I` (`iSupRho_eq_id`,
  the cofinite-`Δ` structure of `iterSys`). For any strict homomorphism `g`, the sequence `g ∘ ρₙ` is
  `g`-independent (the recursion `g∘ρₙ₊₁ = k∘T(g∘ρₙ)∘j`), so `g = ⋃ₙ g∘ρₙ` is forced.

Everything is choice-free where it is data.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Exercise618

/-! ## `∅`-freeness is preserved by `prod` and `iterSys` -/



/-! ## The "cons" description of the Exercise 3.16 isomorphism -/

variable {α : Type*} {V : NeighborhoodSystem α}






/-! ## Bottom-element computations -/




/-! ## The structure isomorphism `i, j` as approximable maps -/





/-! ## Monotonicity of the product action -/



/-! ## The homomorphism operator and the descent chain -/

section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}











end Target

/-! ## Generic chain helpers -/



section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}





/-! ## The fixed-point equation `h = k ∘ T(h) ∘ j` -/


/-! ## Strictness of the descent map -/



/-! ## The homomorphism square `h ∘ i = k ∘ T(h)` -/


end Target

/-! ## The truncation chain `ρₙ` and `⋃ₙ ρₙ = I`

The descent chain for the structure map `i` itself, `ρₙ = (descSeq i)ₙ : 𝒟^∞ → 𝒟^∞`, truncates a
sequence to its first `n` coordinates. Its supremum is the identity (`iSupRho_eq_id`), the key fact
behind uniqueness: every strict homomorphism is determined on the finite truncations. -/



/-! ## Uniqueness of strict homomorphisms -/

section Uniq

variable {γ : Type*} {E : NeighborhoodSystem γ}




end Uniq

/-! ## The endofunctor `T(X) = 𝒟 × X` and `𝒟^∞` as its initial algebra

We package the analysis into the bespoke category `StrictDomainObj` of `∅`-free domains and strict
maps (Exercise 6.17), exactly the setting in which `IsInitial` expresses Scott's universal property.
The fixed domain `𝒟` is an arbitrary `StrictDomainObj`. -/









end Exercise618

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems.Exercise618

set_option linter.unusedVariables false

theorem example_618.{u_2, u_3, u_4, u_5} : ∀ {α : Type u_2} {β : Type u_3} {α' : Type u_4} {β' : Type u_5}
  {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
  {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
  {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
  {f₀ : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀'}
  {f₁ : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁'},
  @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict α α' V₀ V₀' f₀ →
    @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict β β' V₁ V₁' f₁ →
      @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict (Sum α β) (Sum α' β')
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁')
        (@DomainTheory.NeighbourhoodSystems.prodMap α β α' β' V₀ V₁ V₀' V₁' f₀ f₁) :=
  @DomainTheory.NeighbourhoodSystems.Exercise618.isStrict_prodMap

end DomainTheory.NeighbourhoodSystems.Exercise618
