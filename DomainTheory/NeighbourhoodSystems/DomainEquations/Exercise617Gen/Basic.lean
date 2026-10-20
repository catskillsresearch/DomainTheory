/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.coneN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.memCn
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.strBotN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.strElemN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.prependN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.consMapN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tu
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.masterSig
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sumSig
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sinjU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sinjC
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sumMapSig
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tsigMapHom
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.embA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.toCC
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.fromCC
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.ccEquiv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.liftCn
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.descE
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.descF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.descVal
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.descMap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.descStrict
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.descAlgHom
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.CnisInitial
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.CfinIsInitial
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Strn
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_coneN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.coneN_nil
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.coneN_subset_coneN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.coneN_injective
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.coneN_trichotomy
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.memCn_coneN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.memCn_singleton
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.singleton_subset_coneN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.singleton_coneN_nd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.nestedOrDisjointN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_prependN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.prependN_coneN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.prependN_singleton
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.prependN_mono
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.memCn_prependN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.consMapN_rel
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.consMapN_strBot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.consMapN_strElem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.SigTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tc_injective
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tc_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.none_not_mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.none_not_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tu_not_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tc_not_mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tc_mem_jc_ne
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.jc_inter_jc_same
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.jc_inter_jc_ne
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.jU_inter_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.jU_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.jc_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.jc_subset_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.jc_injective
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.jc_eq_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.none_mem_masterSig
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tu_mem_masterSig
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.jU_subset_masterSig
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.jc_subset_masterSig
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.masterSig_inter_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.masterSig_inter_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.eq_masterSig_of_subset
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sumSig_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sumSig_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_subset_jc_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_subset_jU_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sinjU_mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sinjC_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sinjC_mono
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.isStrict_sumMapSig
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sumMapSig_rel
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sumMapSig_sinjU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sumMapSig_sinjC
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sumMapSig_id
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sumMapSig_comp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tsigObj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tsigObj_sys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tsigMapHom_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Tsig
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Tsig_obj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Tsig_map_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_embA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.embA_eq_prependN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.embA_coneN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.embA_singleton
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.memCn_embA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.nil_not_mem_embA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.embA_ne_univ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.embA_inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.embA_inter_ne
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.embA_subset
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.embA_injective
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.memCn_embA_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.singleton_nil_inter_embA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.singleton_nil_ne_univ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.singleton_nil_ne_embA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.memCn_cases
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.CCn
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sumSig_mem_jc_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.toCC_mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.toCC_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.embA_eq_embA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.fromCC_mem_nil
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.fromCC_mem_embA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.fromCC_toCC
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.toCC_fromCC
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.ccEquiv_apply
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.consMapN_mem_embA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.consMapN_not_mem_embA_ne
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.consMapN_not_mem_nil
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.toCC_consMapN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.toCC_strElemN_nil
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cnobj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cnobj_sys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.cnStr
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cnalg
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.not_coneN_subset_singleton
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.coneN_ne_singleton
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.liftCn_strBot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.liftCn_strElem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.map_ext_Cn
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.descF_mono
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.descVal_mono_z
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.descVal_append
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.descMap_hcone
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.descMap_hsing
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.descMap_strBot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.descMap_strElem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_bot_eq_strBotN_nil
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.descMap_strict
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.genKey
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.genKey0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.genKeyBot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.ccEquiv_symm_comp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.ccEquiv_comp_symm
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.rec_determines
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.descMap_satisfiesRec
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.descComm
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.descAlgHom_uniq

@[expose] public section

/-!
# Exercise 6.17 part 2 (Scott 1981, PRG-19) — the generalization `Cₐ ≅ 𝟙 + Σₐ Cₐ`

Example 6.2 / Exercise 6.17 ask for the generalization of `C` corresponding to Scott's `A ≅ Aⁿ + Aⁿ`:
replace the two-letter alphabet `{0,1}` of `C` (`C ≅ 𝟙 + C + C`) by an arbitrary alphabet `A`. The
domain `Cₐ` of *finite or infinite `A`-sequences* then satisfies the domain equation
`Cₐ ≅ 𝟙 + Σ_{a:A} Cₐ` (the `A`-indexed separated sum of copies of `Cₐ`). Instantiating `A := Fin n`
gives **`Cₙ ≅ 𝟙 + n·Cₙ`**; `A := Bool` recovers Example 6.2's `C`.

This module mirrors, generically over an alphabet `A` with decidable equality, the binary development
of `Example44` (the domain), `Example62`/`Example62C` (the sum and the isomorphism) and `Exercise617`
(initiality).

## Stage 1 (this section): the generic domain `Cₐ`

`Strn A = List A`; cones `coneN σ = σA*`; the neighbourhood system `Cn = {σA*} ∪ {{σ}}`; the total
elements `strElemN σ` and partial elements `strBotN σ`; and the successors `consMapN a : Cₐ → Cₐ`
prepending the letter `a`. Everything is the alphabet-generic copy of `Example44`, and the data
(`Cn`, `consMapN`) stays choice-free.
-/

namespace DomainTheory.NeighbourhoodSystems.Exercise617Gen

set_option linter.unusedSectionVars false

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

variable {A : Type} [DecidableEq A]




















/-! ### Prepending a letter: the successors `x ↦ a·x`. -/











/-! ## Stage 2: the `A`-indexed separated sum `Tsig(X) = 𝟙 + Σ_{a:A} X`

The right-hand side of the generalized domain equation. Tokens are `Option (Unit ⊕ (A × β))`: a
fresh basepoint `Λ = none`, the lone `𝟙`-token `tu = some (inl ())`, and the `A`-indexed family of
tagged copies `tc a t = some (inr (a, t))`. This is the alphabet-generic analogue of `Example62C`'s
three-way `sum3 unitSys C C` (`= 𝟙 + C + C`), the index `Bool` being replaced by `A`. -/

section SumSig

universe v

variable {β : Type v} {γ : Type v}






















variable (V : NeighborhoodSystem β)


variable {V}











/-! ### Shape lemmas: no nesting through the wrong tag. -/

variable {h : ∀ X, V.mem X → X.Nonempty}



/-! ### The canonical injections `𝟙 ↪ 𝟙+Σ_a V` and `V ↪ 𝟙+Σ_a V` (the `a`-th copy). -/






end SumSig

/-! ### The sum map `Σ f = I_𝟙 + Σ_a f` and its functoriality. -/

section SumMapSig

universe v

variable {β₀ β₁ β₂ : Type v}
  {V₀ : NeighborhoodSystem β₀} {V₁ : NeighborhoodSystem β₁} {V₂ : NeighborhoodSystem β₂}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}








end SumMapSig

/-! ## The endofunctor `Tsig(X) = 𝟙 + Σ_a X` on the `∅`-free category. -/








/-! ## Stage 3: the domain equation `Cₐ ≅ 𝟙 + Σ_a Cₐ`.

The alphabet-generic analogue of `Example62C` (`C ≅ 𝟙 + C + C`). Prepending the letter `a` to a
neighbourhood gives `embA a X`; a `Cₐ`-neighbourhood is the master, the terminator `{Λ}`, or some
`a`-copy `aX`, exactly the shapes of the `A`-indexed sum `𝟙 + Σ_a Cₐ`. -/

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]


















/-! ### The sum target `𝟙 + Σ_a Cₐ` and its inversion lemmas. -/



/-! ### The forward half `toCC : |Cₐ| → |𝟙 + Σ_a Cₐ|`. -/





/-! ### The inverse half `fromCC : |𝟙 + Σ_a Cₐ| → |Cₐ|`. -/




/-! ### The two halves are mutually inverse. -/





/-! ### Bridging the isomorphism to the successors `consMapN`. -/






end Iso

/-! ## `Cₐ` as a `Tsig`-algebra. -/

section Algebra

variable {A : Type} [DecidableEq A] [Inhabited A]





end Algebra

/-! ## The `liftCn` combinator: an approximable map out of `Cₐ` (generic `Exercise419.liftC`). -/

section Lift

variable {A : Type} [DecidableEq A] [Inhabited A] {β : Type}







end Lift

/-! ## Initiality of `(Cₐ, i)`: the unique homomorphism into any `Tsig`-algebra. -/

section Initial

variable {A : Type} [DecidableEq A] [Inhabited A] (B : TAlgebra (Tsig A))















/-! ### The homomorphism square and uniqueness. -/











end Initial


/-! ## Instantiation: `Cₙ ≅ 𝟙 + n·Cₙ` over the `n`-letter alphabet `Fin (n+1)`.

Taking `A := Fin (n+1)` recovers Scott's `Cₙ`: the domain of finite-or-infinite sequences over an
`(n+1)`-letter alphabet, satisfying `Cₙ ≅ 𝟙 + (n+1)·Cₙ`. (For `n = 1`, `Fin 2 ≃ Bool` recovers
Example 6.2's `C ≅ 𝟙 + C + C`.) -/

end DomainTheory.NeighbourhoodSystems.Exercise617Gen
