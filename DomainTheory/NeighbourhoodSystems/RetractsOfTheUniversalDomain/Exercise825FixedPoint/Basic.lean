/-ai
This file gathers and re-exports the ingredients of the fixed-point solution: Proposition 8.10(b), the combinators of Table 5.5, the fixed-point method of Exercise 8.23, the effective givenness of infinite iterates, the product isomorphism of infinite powers, the embedding into an infinite power, the abstract closing argument, the constant-function embedding, a computable presentation of the infinite power of the universal domain, the injection and projection and their composite identity, the combinator and the isomorphism of its fixed set with that power, the isomorphism of a fixed neighbourhood with a fixed set, the joint evaluator and its domain, the two curries, the continuous operator, and the arrow domain. The commentary records how these assemble a domain isomorphic to the function space into the infinite power of the universal domain, and how the universal domain embeds into that solution.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Pow
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Embed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Closing
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825FixedPoint.presentationIterU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825FixedPoint.cInj
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825FixedPoint.cProj
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825FixedPoint.cCombinator
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825FixedPoint.cElementIso
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825FixedPoint.fixedNbhd_elementIso_fix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825FixedPoint.RMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825FixedPoint.curryOnceC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825FixedPoint.lamOp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825FixedPoint.tOpMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825FixedPoint.TArrow
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825FixedPoint.cProj_comp_cInj
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825FixedPoint.RDom

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.NeighborhoodSystemu2eIsEffectivelyGivenu2etoS
@[expose] public section

/-!
# Exercise 8.25 (Scott 1981, PRG-19, §8), step 3 — solving `D ≅ D → 𝒰^∞` by the fixed-point method

Scott's hint: solve `D ≅ D → 𝒰^∞` "using the methods of Exercise 8.23". This file supplies the
one remaining ingredient `Exercise825Closing.lean` needs: a concrete `D` with `D ≅ D → V` for
`V := iterSys 𝒰 = 𝒰^∞`.

## Strategy

Exercise 8.23's abstract machinery (`Exercise823.isFinitaryProjection_fixOp`,
`Exercise823.fixedDomain_fixOp_iso_T`) turns "a continuous operator `t : (𝒰→𝒰) → (𝒰→𝒰)` sending
finitary projections to finitary projections, with `Fix(t(a)) ≅ T(a)`" into a genuine solution
`D_{‖t‖} ≅ T(‖t‖)`. We instantiate `T(a) := D_a → D_c` (Proposition 8.10(b)'s `→`-case) for a
*fixed* finitary projection `c : 𝒰 → 𝒰` with `Fix(c) ≅ 𝒰^∞`, so `t(a) := a → c = arrowComb a c`
(`a` varying, `c` fixed) and `T(‖t‖) = D_{‖t‖} → D_c ≅ D_{‖t‖} → 𝒰^∞`.

## Building `c` with `Fix(c) ≅ 𝒰^∞`

`𝒰^∞ = iterSys 𝒰` is effectively given (`Exercise715.iterSys_isEffectivelyGiven`), so Theorem
8.8(b)'s `theorem_8_8_b_strong` gives a projection pair `i : 𝒰^∞ → 𝒰`, `j : 𝒰 → 𝒰^∞` with
`j∘i = I` and `i∘j ≤ I`. Setting `c := i∘j`, Proposition 8.10(b)'s generic
`elementIsoOfProjectionPair`/`isFinitary_of_projectionPair` machinery gives `IsFinitaryProjection c`
and `𝒰^∞ ≅ Fix(c)` directly (`cElementIso`), and combined with `Proposition82.elementIso` applied
to `fixedNbhd c ◁ 𝒰` (Theorem 8.5/8.6's usual bridge, `inj_comp_proj_eq_self`) gives
`fixedNbhd c ≅ 𝒰^∞` (`fixedNbhd_cCombinator_isomorphic`).

## Building `t` as a genuinely continuous self-map of `funSpace 𝒰 𝒰`

This is the technical crux: `a ↦ arrowComb a c` must be *continuous in `a`* (an element of
`funSpace 𝒰 𝒰`), not just a family of maps indexed by `a`. We build it from Table 5.5's `compC`/
`curryC`/`evalC` combinators via a joint three-variable evaluator

`R(ψ, φ, x) := c(φ(ψ(x)))`,   `ψ, φ ∈ |𝒰→𝒰|`, `x ∈ |𝒰|`,

purely as a composite of `evalMap`/`proj`/`paired`/`comp` (`RMap`) — manifestly continuous jointly
in all three arguments since `evalMap` itself is. Currying `R` twice (`curryOnceC`, then
`curryC`, giving `lamOp c : (𝒰→𝒰) → ((𝒰→𝒰) → (𝒰→𝒰))`, an element of a fourth-order function
space) recovers Definition 8.9's `lamComb a c = expMap a c` at each fixed `a` (`toApproxMap_lamOp`,
checked against `Proposition810b.toApproxMap_toElementMap_expMap`). Composing on the outside with
the *fixed* Hom-functor action `expMap jArrow iArrow` (conjugating by the fixed projection pair
`𝒰 ⇄ (𝒰→𝒰)`) produces `t := tOpMap c`, and unwinds to exactly `arrowComb a c` at every `a`
(`tOp_tOpMap`) — so `t` really is Definition 8.9's `arrowComb (-) c`, made continuous.

## Assembling the theorem

`ht_tOpMap` transports Proposition 8.10(b)'s `finitaryProjection_arrowComb` along `tOp_tOpMap` to
get Exercise 8.23's hypothesis; `Exercise823.isFinitaryProjection_fixOp` and
`Exercise823.fixedDomain_fixOp_iso_T` (instantiated at `T(a) := funSpace (fixedNbhd a)
(fixedNbhd c)`, via `arrowComb_elementIso`) hand us `D ≅ D → (fixedNbhd c) ≅ D → 𝒰^∞` for
`D := fixedNbhd (fixOp t)` (`Dsol_isomorphic_funSpace_cCombinator`). Combined with
`Exercise825Pow.pow_prod_isomorphic` (transported along `fixedNbhd c ≅ 𝒰^∞`, giving
`hVV_cCombinator : (fixedNbhd c) × (fixedNbhd c) ≅ fixedNbhd c`), `Exercise825Closing`'s abstract
closing argument finishes: `D ≅ D → D` (`exercise_8_25_main`).

**Non-triviality/universality** (`U_trianglelefteq_Dsol`): chaining `𝒰 ⊴ 𝒰^∞`
(`Exercise825Embed.trianglelefteq_iterSys`), `𝒰^∞ ≅ fixedNbhd c` (hence `⊴`), the *general* fact
`𝒱 ⊴ (𝒟 → 𝒱)` (`Exercise820.trianglelefteq_funSpace_const`, the constant-function embedding) at
`𝒱 := fixedNbhd c`, `𝒟 := D`, and `D → (fixedNbhd c) ≅ D` (from `Dsol_isomorphic_funSpace_cCombinator`,
reversed) gives `𝒰 ⊴ D`: the solution domain genuinely contains a copy of the universal domain `𝒰`,
so it is non-trivial (matching Scott's remark).

Axiom footprint: everything here mentions `U`, so — like `Definition89.lean`/`Proposition810b.lean`
— it inherits `U`'s own `Classical.choice` footprint (`⊆ {propext, Classical.choice, Quot.sound}`),
confirmed not new.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

/-! ## Building `c`, a finitary projection with `Fix(c) ≅ 𝒰^∞` -/








/-! ## The joint evaluator `R(ψ, φ, x) := c(φ(ψ(x)))`, built from `evalMap`/`proj`/`paired` -/



/-! ## Currying `R` twice: `lamOp c : (𝒰→𝒰) → ((𝒰→𝒰) → (𝒰→𝒰))`, recovering `lamComb (-) c` -/



/-! ## `t := tOpMap c`, conjugating `lamOp c` by the fixed pair `𝒰 ⇄ (𝒰→𝒰)` -/


/-! ## Assembling `D ≅ D → 𝒰^∞` -/


/-! ## Non-triviality: `𝒰 ⊴ D` -/
end DomainTheory.NeighbourhoodSystems
