/-ai
This module gathers and re-exports the Exercise 6.23 development of the syntactic domain of expressions. It brings together the Kleene generator of a rooted functor expression and its fixed-point properties, the iterated tower, its chain, and its colimit, the expression functor T(X) = N ⊕ ((X × X) + (X × X)) and the structure isomorphism of the colimit Exp, the category of empty-free domains over strings and strict maps, the algebra structure and the Kleene evaluation homomorphism, and the projection-pair and projection-chain argument that this homomorphism is the unique algebra homomorphism.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gFix
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gGen
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gTower
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gColim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.Texp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.Exp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gFunctorMap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.isoOfObjEq
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.ExpIso
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.algStr
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.expInv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.expHom
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.descRel
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.descMap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.descAlgHom
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.rho
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.iSupRho
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.ExpInitial
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gFix_nil_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gFix_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gFix_fixed
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gGen_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gBase
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gTower_zero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gTower_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gChain
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gTower_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gTower_le
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.mem_gColim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gColim_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gTower_sub_colim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.ext
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gColim_obj_sys_eq
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gColim_obj_eq
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.Texp_rooted
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.Exp_structure_eq
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.BasicInst28
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.id_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.comp_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gFunctor
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gFunctor_obj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gFunctorMap_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.TexpF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.ExpAlg
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.algStr_strict
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.expInv_strict
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.expInv_comp_expHom
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.descRel_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.descRel_isStrict
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.constBot_le
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.descRel_le_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.descRel_mono
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.descDir
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.descMap_rel
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.descMap_isStrict
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.descDirLe
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.descMap_is_sup
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.descMap_fix
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.descComm
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.inj_isStrict
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.self_inj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.self_proj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.sumMapTok_inj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.sumMapTok_proj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.prodMapTok_inj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.prodMapTok_proj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.oplusMapTok_inj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.oplusMapTok_proj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.otimesMapTok_inj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.otimesMapTok_proj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.map_inj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.map_proj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.isoOfObjEq_hom_rel
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.isoOfObjEq_inv_rel
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.expHom_rel
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.expInv_rel
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.expSub
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.rho_rel
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.rho_mono
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.iSupRho_eq_id
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.rho_zero_rel
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.map_rho_eq
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.key_rho
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gcomp_rho_zero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gcomp_rho_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gcomp_rho_eq
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.descMap_eq_algHom
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.algHom_ext

@[expose] public section

/-!
# Exercise 6.23 (Scott 1981, PRG-19, §6) — the syntactic domain of expressions

> **EXERCISE 6.23.** Construe the initial solution to
> `Exp ≅ N ⊕ ((Exp × Exp) + (Exp × Exp))`
> as a "syntactical domain" of expressions generated from infinitely many "variables" by means of two
> binary "operation symbols". Given an algebra `D` with two operations `u : D×D → D` and
> `v : D×D → D`, show how any strict map `s : N → D` determines a unique map `val(s) : Exp → D` that
> can be regarded as the "evaluation of an expression".

The right-hand functor is `T(X) = N ⊕ ((X×X) + (X×X))`, i.e. in the algebra `GExpr` of Exercise 6.21,
`Texp N = .oplus (.const N) (.sum (.prod .var .var) (.prod .var .var))`. Reading the structure map
`k : T(Exp) → Exp` of an algebra through the universal properties of `⊕`, `+`, `×`:

* the `⊕ N` summand gives a strict **variable map** `s : N → Exp` (the "infinitely many variables"
  are the tokens / points of `N`);
* the two `(Exp × Exp)` summands, combined by `+`, give two binary **operation symbols**
  `u, v : Exp × Exp → Exp`.

So an algebra of this functor is exactly *a domain `D` with a strict `s : N → D` and two binary
operations `u, v : D×D → D`*, and the unique homomorphism `val(s) : Exp → D` is Scott's "evaluation
of an expression": it sends a variable to its value under `s`, and an `u`/`v`-node to the `u`/`v` of
the values of its two subexpressions.

## This module (Phase 1 — the domain `Exp` itself)

Following Scott's standing restriction in Exercises 6.19–6.23 to `∅`-free systems over `{0,1}*` and
*strict* maps (`ScottSys`), and following the structure of **Theorem 6.14** (the initial solution is
the iterated colimit `𝒟 = ⋃ₙ Tⁿ({Γ})`), we build the concrete solution domain **for any rooted
`GExpr` functor** `T`:

* `gFix T = ⋃ₙ gFunⁿ({Λ})` — the token set (Exercise 6.20/6.21 fixed point `Γ = tok(T({Γ}))`);
* `gTower T n = Tⁿ({Γ})` — the iterated-functor tower of `∅`-free systems over `Str`;
* `gColim T = ⋃ₙ Tⁿ({Γ})` — the colimit system, with `gColim_obj_eq : T(gColim) = gColim` (the
  structure map is the **identity**, since the two systems are literally equal — no carrier transport
  is needed because `ScottSys` keeps the token type fixed at `Str`).

Instantiating at `Texp N` gives `Exp N := gColim (Texp N)` together with the domain-equation
**isomorphism** `Exp ≅ N ⊕ ((Exp×Exp)+(Exp×Exp))` (`Exp_structure_eq`). The algebra decomposition
(`s`, `u`, `v`) and the unique evaluation homomorphism `val(s)` (initiality) are developed in later
phases.

Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`); the colimit is genuine data
built without `Classical.choice` (the generator `Γ` is the *explicit* Kleene union, not an
existential witness).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

/-! ## The generator `Γ = ⋃ₙ gFunⁿ({Λ})` (the Exercise 6.20/6.21 fixed point, as data) -/

/-! ## The iterated-functor tower `Tⁿ({Γ})` -/

/-! ## The colimit `𝒟 = ⋃ₙ Tⁿ({Γ})` -/

/-! ## The structure isomorphism `T(𝒟) = 𝒟` -/

/-! ## The functor of Exercise 6.23 and the syntactic domain `Exp` -/

/-! ## Phase 2 — the strict-map category, the endofunctor `T`, and the algebra `Exp`

Following Scott (and Exercise 6.17's `StrictDomainObj`), but over the *fixed* token type `Str`: the
objects are `ScottSys` (∅-free systems over `Str`), the morphisms are **strict** approximable maps.
Because every object lives over `Str`, all carrier equalities are `rfl` and there is no `HEq`
transport (the obstruction that made the abstract Theorem 6.14 unusable). The functor `Texp N` then
becomes a genuine `Endofunctor` of this category, and the colimit `Exp` of Phase 1 — together with the
structure equality `T(Exp) = Exp` — is a `T`-algebra. -/

/-! ## Phase 3 — the evaluation homomorphism `val(s)` (existence)

Given any algebra `B = (D, k)` of `T(X) = N ⊕ ((X×X)+(X×X))` — i.e. a domain `D` carrying (through the
universal properties of `⊕`,`+`,`×`) a strict variable map `s : N → D` and two binary operations
`u, v : D×D → D` — we build a `T`-algebra homomorphism `val : Exp → D`. This is Scott's *"evaluation
of an expression"*.

Since Phase 1's structure map `i : T(Exp) → Exp` is the **identity** (`Exp_structure_eq`), the
homomorphism equation `val ∘ i = k ∘ T(val)` is the fixed-point equation `val = k ∘ T(val) ∘ j`
(`j = i⁻¹`). We solve it directly by the Kleene iteration `valₙ` (`val₀ = ⊥`,
`valₙ₊₁ = k ∘ T(valₙ) ∘ j`) and take `val = ⋃ₙ valₙ`. The fixed-point property uses *continuity on
maps* (`GExpr.map_continuous`: `T(⋃ valₙ) = ⋃ T(valₙ)`); no projection machinery is needed for
existence. (Uniqueness — initiality — is the remaining Phase 4.) -/

/-! ## Phase 4 — uniqueness of `val(s)` and initiality of `Exp`

Scott proves homomorphisms out of the iterated colimit are unique by showing they are *determined on
the finite elements*: the projection chain `ρₙ = iₙ ∘ jₙ` (Proposition 6.12's pair for
`Texpⁿ({Γ}) ◁ Exp`) satisfies `T(ρₙ) = ρₙ₊₁` and `⋃ₙ ρₙ = I_Exp`, so any homomorphism `g` equals
`⋃ₙ g ∘ ρₙ`, a sequence that is forced by the recursion (independent of `g`). The crux is the
*concrete* "monotone on domains" content (Definition 6.13): the functor `Texp` carries the canonical
6.12 projection pair of `D ◁ E` to that of `T(D) ◁ T(E)` — here a genuine **equality** of maps over
`Str` (no `HEq` carrier transport, the whole point of staying in `ScottSys`).

This section establishes that crux as `GExpr.map_inj`/`GExpr.map_proj` (by induction over the six
functor constructors), then mirrors Theorem 6.14's uniqueness argument concretely. -/

/-! ### Proposition 6.12 helpers: the projection pair is strict, and trivial on `D ◁ D` -/

/-! ### The functor carries projection pairs: the token-level lemmas -/

variable {A₀ A₁ B₀ B₁ : ScottSys}

/-! ### The crux (Definition 6.13, concrete): `T` carries the 6.12 projection pair

This is the *monotone on domains* content of Definition 6.13, but here a genuine **equality** of maps
over the single token type `Str` (no `HEq` carrier transport): the functor `T = GExpr` sends the
injection/projection of `D ◁ E` to the injection/projection of `T(D) ◁ T(E)`. Proved by induction
over the six constructors using the token-level lemmas just established. -/

/-! ### The identity structure isomorphism, relationally -/

/-! ### The projection chain `ρₙ = iₙ ∘ jₙ` and `⋃ₙ ρₙ = I_Exp` -/

/-! ### The crux equation `ρₙ₊₁ = i ∘ T(ρₙ) ∘ j` -/

/-! ### `g`-independence of `g ∘ ρₙ` and uniqueness -/
end Exercise619
end DomainTheory.NeighbourhoodSystems
