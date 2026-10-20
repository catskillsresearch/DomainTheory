/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition63
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516
public import DomainTheory.NeighbourhoodSystems.DomainEquations.StrictDomainObj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sumMap3
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.tcMapHom
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descE
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descVal
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617.descMap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descStrict
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617.descAlgHom
public import DomainTheory.NeighbourhoodSystems.DomainEquations.CisInitial
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Inst3
public import DomainTheory.NeighbourhoodSystems.DomainEquations.id_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.comp_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sum3_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.tcObj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.tcObj_sys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_subset_j0_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_subset_j1_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_subset_j2_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.isStrict_sumMap3
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sumMap3_id
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sumMap3_comp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj0_mem_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj1_mem_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj2_mem_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj1_mono
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj2_mono
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sumMap3_sinj0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sumMap3_sinj1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sumMap3_sinj2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Tc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Tc_obj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Tc_map_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.isStrict_ofIso
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Cobj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.cStr
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Calg
public import DomainTheory.NeighbourhoodSystems.DomainEquations.ccEquiv_apply
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consMap_mem_embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consMap_not_mem_embBit_ne
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consMap_not_mem_nil
public import DomainTheory.NeighbourhoodSystems.DomainEquations.toCC_consMap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.toCC_strElem_nil
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descF_mono
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descVal_mono_z
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descVal_append
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descMap_hcone
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descMap_hsing
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descMap_strBot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descMap_strElem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.C_bot_eq_strBot_nil
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descMap_strict
public import DomainTheory.NeighbourhoodSystems.DomainEquations.genKey
public import DomainTheory.NeighbourhoodSystems.DomainEquations.genKey0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.genKeyBot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.ccEquiv_symm_comp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.ccEquiv_comp_symm
public import DomainTheory.NeighbourhoodSystems.DomainEquations.rec_determines
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descMap_satisfiesRec
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descComm
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descAlgHom_uniq

@[expose] public section

/-!
# Exercise 6.17 (Scott 1981, PRG-19, §6) — the algebras for which `C` is initial

> **EXERCISE 6.17.** What are the algebras for which `C` is initial? If `A` of 6.2 is a generalization
> of `B`, what is the corresponding generalization of `C`? Prove that it exists and explain what are
> the algebras involved.

`C` (Example 4.4: finite-or-infinite binary sequences) satisfies the domain equation
`C ≅ {{Λ}} + C + C` (Example 6.2, `Example62C.lean`). So `C` is a solution of the domain equation for
the functor

`T(X) = 𝟙 + X + X`   (one terminator + two successor copies).

This module proves that **`C` is the *initial* `T`-algebra**: for every `T`-algebra `(E, k)` there is a
*unique* homomorphism `C → E`. Concretely a `T`-algebra is a strict map `k : 𝟙 + E + E → E`, which by
the universal property of the separated sum is the same data as

* a distinguished element `e ∈ |E|` (the image of the terminator `𝟙`), and
* two strict endomaps `f₀, f₁ : E → E` (the two successor branches);

so **the algebras for which `C` is initial are the domains carrying a point and two strict unary
operations**, and the unique homomorphism `C → E` interprets a finite-or-infinite binary sequence
`b₀b₁b₂…` as `f_{b₀}(f_{b₁}(… e …))`.

## Why a bespoke category of `∅`-free domains

Scott's separated sum `𝒟₀ + 𝒟₁` (Exercise 3.18) is a neighbourhood system **only** under the standing
assumption `∅ ∉ 𝒟` (an empty neighbourhood of one summand would become a spurious consistency witness
for the other tag, breaking `inter_mem`). Consequently the functor `T(X) = 𝟙 + X + X` does **not**
extend to a total endofunctor of the all-systems category `DomainObj`, and the existence Theorem 6.14
(stated over `DomainObj`) cannot be instantiated directly.

Following Scott — who restricts to the category of `∅`-free systems and *strict* maps in Exercise 6.19
— we instantiate the abstract categorical vocabulary (Definitions 6.3–6.5) on the bespoke object type
`StrictDomainObj` of neighbourhood systems with **no empty neighbourhood**, with **strict approximable
maps** as morphisms. The functor `T` then reuses the existing `sum3` (Example 6.2, the genuine
three-way separated sum) and a three-way sum map, and initiality of `C` is proved **directly** (we
construct the homomorphism and prove its uniqueness by the finite-approximant argument), rather than
routing through the colimit construction of Theorem 6.14.

Everything is choice-free where it is data; the homomorphism/uniqueness layer reuses the project's
established machinery.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

/-! ## The category of `∅`-free domains and strict maps -/





/-! ## The functor `T(X) = 𝟙 + X + X` on objects -/




/-! ### Membership-shape lemmas for `sum3` (no nesting through the wrong tag) -/

section ShapeLemmas

open Example62C

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ} {h₀ : ∀ X, V₀.mem X → X.Nonempty}
  {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty} {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}




end ShapeLemmas

/-! ### The three-way sum map `f₀ + f₁ + f₂` -/

section SumMap3

open Example62C

variable {α β γ α' β' γ' : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
  {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'} {V₂' : NeighborhoodSystem γ'}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}
  {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}
  {h₂' : ∀ Z, V₂'.mem Z → Z.Nonempty}





end SumMap3

/-! ### The canonical injections `D_i ↪ D₀+D₁+D₂` -/

section SumInj

open Example62C

variable {α β γ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}







end SumInj

/-! ### Monotonicity of the injections, and the action of `f₀+f₁+f₂` on them -/

section SumInjMap

open Example62C

variable {α β γ α' β' γ' : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
  {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'} {V₂' : NeighborhoodSystem γ'}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}
  {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}
  {h₂' : ∀ Z, V₂'.mem Z → Z.Nonempty}






end SumInjMap

/-! ## The functor `T(X) = 𝟙 + X + X` -/





/-! ## `C` as a `T`-algebra -/





/-! ## Initiality of `(C, i)`: the unique homomorphism into any `T`-algebra

We first relate the domain-equation isomorphism `toCC = ccEquiv` to the separated-sum injections:
the terminator `Λ̂` lands on the `𝟙`-copy, and prepending a bit (`consMap b`) lands on the `b`-th
`C`-copy. -/

namespace Example62C

open Example44 ExampleB Example62







end Example62C

/-! ### The homomorphism `desc : C → E` for a `T`-algebra `B = (E, k)` -/

section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)















/-! ### The homomorphism square and uniqueness -/











end Initial


end DomainTheory.NeighbourhoodSystems
