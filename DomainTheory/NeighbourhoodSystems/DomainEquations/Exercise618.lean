/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq
public import DomainTheory.NeighbourhoodSystems.DomainEquations.jmap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.imap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descOp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descSeq
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise618.descMap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.kHead
public import DomainTheory.NeighbourhoodSystems.DomainEquations.prodObj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.prodMapHom
public import DomainTheory.NeighbourhoodSystems.DomainEquations.prodFunctor
public import DomainTheory.NeighbourhoodSystems.DomainEquations.iterObj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.iterAlg
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise618.descAlgHom
public import DomainTheory.NeighbourhoodSystems.DomainEquations.iterIsInitial
public import DomainTheory.NeighbourhoodSystems.DomainEquations.prod_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.iterSys_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.iterProdIso_apply
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq_zero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.iterProdIso_symm_pair
public import DomainTheory.NeighbourhoodSystems.DomainEquations.iterBot_eq
public import DomainTheory.NeighbourhoodSystems.DomainEquations.component_bot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.pair_bot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.isStrict_imap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.jmap_comp_imap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.prodMap_idMap_mono
public import DomainTheory.NeighbourhoodSystems.DomainEquations.toElementMap_le_of_le
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descOp_apply
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descOp_mono
public import DomainTheory.NeighbourhoodSystems.DomainEquations.constBot_le
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descSeq_mono_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descSeq_mono
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descSeq_dir
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descMap_toElementMap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.chain_le_of_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.succChainDir
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descSeqEltMono
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descMap_eq
public import DomainTheory.NeighbourhoodSystems.DomainEquations.kHead_apply
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descMap_fix
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descSeq_strict
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise618.descMap_strict
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descMap_comm
public import DomainTheory.NeighbourhoodSystems.DomainEquations.rho_apply
public import DomainTheory.NeighbourhoodSystems.DomainEquations.iSupRho_eq_id
public import DomainTheory.NeighbourhoodSystems.DomainEquations.gcomp_rho_zero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.gcomp_rho_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.comm_unique
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
