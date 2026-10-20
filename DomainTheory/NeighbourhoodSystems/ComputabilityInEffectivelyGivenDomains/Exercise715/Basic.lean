/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.ScottPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.inclShuffle
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.swapPair
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.IsEffectivelyGivenS
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.toScott
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.IsComputableMapS
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashEnum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashProj₀
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashProj₁
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashPaired
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashMap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osumEnum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osumPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osumInMap₀
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osumInMap₁
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osumOutMap₀
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osumOutMap₁
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osumMap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.iterIdx
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.iterEnum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.interG
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.iterInter
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.iterPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.primrec_inclShuffle
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.primrec_swapPair
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.incl_computable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.eq_computable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashEnum_proper
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashEnum_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashEnum_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashEnum_subset_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashEnum_eq_prodNbhd_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashEnum_eq_eff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.proper₀_dec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.proper₁_dec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashPresentation_X
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashProj₀_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashProj₁_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashPaired_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osum_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osumEnum_left
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osumEnum_right
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osumEnum_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osumEnum_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osumEnum_subset_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osumEnum_nonempty
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osum_eq_master_of_inj₀master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osum_eq_master_of_inj₁master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osumPresentation_X
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osum_mem_subset_inj₀
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osum_mem_subset_inj₁
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.fiber_iterEnum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.iterIdx_ge
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.iterEnum_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.iterEnum_inter_eq_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.iterInter_idx_lt
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.iterInter_idx_ge
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.iterEnum_cons_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.exists_list_fiber
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.primrec_iterIdx_proj
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.primrec_interG

@[expose] public section

/-!
# Exercise 7.15 (Scott 1981, PRG-19, §7) — effective givenness of `⊗`, `⊕`, `D^∞`

> **EXERCISE 7.15.** Finish the proof of 7.4 and establish similar results for the constructs
> `(D₀ ⊗ D₁)`, `(D₀ ⊕ D₁)` and `D^∞`. Take into account the various appropriate combinators.

Theorem 7.4 (the separated `+` and `×`) is already complete in `Theorem74.lean`, with all
combinators (`projᵢ`, `inᵢ`, `outᵢ`, `⟨f,g⟩`, `f×g`, `f+g`). This file establishes the analogous
results for the three remaining constructs.

## Scott's bare Definition 7.1 vs. the project's "acceptable" presentation

The **smash product** `⊗` and the **coalesced sum** `⊕` *delete the improper tagged copies*
(`0Δ₀`, `1Δ₁`) and re-route them to the master — this is the bottom-collapse that distinguishes them
from the separated `×`/`+`. That re-routing has a sharp consequence for *effective* presentations:

> A primitive-recursive intersection function `inter` (as carried by the project's
> `ComputablePresentation`) **cannot exist** for `⊗`/`⊕`. Concretely, take `a` proper and `b`
> "secretly the master" because one factor is improper while the other is a *V₀-inconsistent* proper
> neighbourhood. Then `(a,b)` is consistent (their intersection is a genuine member), so `inter`
> would have to *detect that `b` is secretly the master* — i.e. decide properness (`Xb = Δ₀`?), a
> recursively decidable but **not primitive-recursive** set-equality test.

Scott's actual **Definition 7.1** only asks that the two relations (i) `Xₙ ∩ Xₘ = X_k` and (ii)
consistency `∃k. X_k ⊆ Xₙ ∩ Xₘ` be *recursively decidable*; it does **not** require a primrec
`inter` (that is a project strengthening, needed only for the function space, Theorem 7.5). So we
introduce Scott's literal notion as `ScottPresentation` and prove `⊗`/`⊕` effectively given with
respect to it. Both of (i),(ii) *are* recursively decidable for `⊗`/`⊕` — they reduce to boolean
combinations of the components' relations together with the (recursively decidable) properness tests.

**Choice discipline.** `ScottPresentation` and the `D^∞` results are choice-free. For `⊗`/`⊕` the
*only* classical input is the **enumeration** `X`, which must branch on the (set-equality) properness
test; we localise `Classical.choice` to that one field (`smashEnum`/`osumEnum`). The recursively
decidable relations (i),(ii) are proved **choice-free** by destructuring the components' deciders.

`D^∞ = iterSys D` (Exercise 3.16) is *uniform* (every cylinder is a genuine member, no deletion), so
it admits a full `ComputablePresentation` and is treated choice-free in the existing interface, with
the coordinate-projection combinators `projN`/`head` computable.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}

/-! ## Scott's bare presentation (Definition 7.1, no primitive-recursive `inter`)

This is the literal content of Definition 7.1: an enumeration with the two relations recursively
decidable. It is exactly `ComputablePresentation` minus the `inter`/`masterIdx` data fields. -/


namespace ScottPresentation

variable {V : NeighborhoodSystem α} (P : ScottPresentation V)







end ScottPresentation




/-! ## The smash product `𝒟₀ ⊗ 𝒟₁` is effectively given (Scott's Definition 7.1)

`smash V₀ V₁` (`Exercise510.lean`) over `α ⊕ β` has neighbourhoods the master `prodNbhd Δ₀ Δ₁`
together with the *proper* products `prodNbhd X Y` (`X ≠ Δ₀`, `Y ≠ Δ₁`). We enumerate it by pairs of
component indices, re-routing improper pairs to the master. The re-routing is the only classical
input (it branches on the set-equality `Xₙ = Δ₀?`). The two relations (i),(ii) are choice-free
recursively decidable. -/

open Exercise510

section Smash

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)


variable {P₀ P₁}







variable (P₀ P₁)





/-! ### Projections and the strict pairing for `⊗` (the `×`-analogue combinators).

The smash product carries the same *projections* `proj₀`/`proj₁` as the separated product (a smash
member is still a product neighbourhood `prodNbhd A B`, and `Sum.inl ⁻¹' (prodNbhd A B) = A`) and a
*strict pairing* `⟨a, b⟩⊗ : 𝒟₂ → 𝒟₀ ⊗ 𝒟₁`. Because the smash deletes the improper products, the
pairing forces *proper* image factors and otherwise lands on the master. All three are computable:
the projections by `smashEnum_eq_eff` + `incl_computable`, the pairing by `a`,`b`'s r.e. relations on
the (raw) codomain coordinate indices together with the codomain properness tests. -/







/-! ### The appropriate combinator for `⊗`: the functorial action `f ⊗ g`.

The smash product is a (bi)functor; `smashMap f g : 𝒟₀ ⊗ 𝒟₁ → 𝒟₀' ⊗ 𝒟₁'` is the coalesced analogue
of Theorem 7.4's `f × g` (`prodMap`). Because the smash collapses bottoms, the relation forces
*proper* image factors (`A' ≠ Δ₀'`, `B' ≠ Δ₁'`) and otherwise lands on the master (the strict
collapse). It is a genuine `ApproximableMap` and is **computable**: on the effective product indices
its relation decodes to `f`'s and `g`'s r.e. relations together with the codomain properness tests. -/

section SmashFunctor

variable {α' β' : Type*} {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}


end SmashFunctor

end Smash

/-! ## The coalesced sum `𝒟₀ ⊕ 𝒟₁` is effectively given (Scott's Definition 7.1)

`𝒟₀ ⊕ 𝒟₁` (Exercise 6.21, here over `Option (α ⊕ β)`) is the separated sum `+` with the *improper*
tagged copies `0Δ₀`, `1Δ₁` deleted (the two bottoms identified). As with `⊗`, the enumeration must
re-route improper copies to the master (the sole classical input), while the relations (i),(ii) are
choice-free recursively decidable. -/

section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)



variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)


variable {P₀ P₁}








/-! ### The appropriate combinators for `⊕`: injections `in₀`/`in₁` and projections `out₀`/`out₁`.

These are the coalesced analogues of Theorem 7.4's separated-sum combinators (`Exercise318`'s
`inMap₀`/`outMap₀`), re-housed over `osum` (whose members are the *proper* tagged copies + master).
Each is a genuine `ApproximableMap` and is **computable** (`IsComputableMapS`): the neighbourhood
relations decode, tag-by-tag, to slices of the components' `incl_computable` together with the
recursively-decidable properness tests `proper₀_dec`/`proper₁_dec`. -/

variable {h₀ h₁}







variable (P₀ P₁)


/-! ### The appropriate combinator for `⊕`: the functorial action `f ⊕ g`.

`osumMap f g : 𝒟₀ ⊕ 𝒟₁ → 𝒟₀' ⊕ 𝒟₁'` is the coalesced analogue of Theorem 7.4's `f + g` (`sumMap`).
The coalesced relation additionally forces the image copy to be *proper* (`Y' ≠ Δ'`); otherwise the
strict collapse routes to the master. It is a genuine `ApproximableMap` and is **computable**. -/

section CoalescedFunctor

variable {α' β' : Type*} {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}
  (h₀' : ∀ X, V₀'.mem X → X.Nonempty) (h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty)




end CoalescedFunctor

end Coalesced

/-! ## The infinite iterate `D^∞` is effectively given (full `ComputablePresentation`)

`D^∞ = iterSys V` (Exercise 3.16) is *uniform*: a neighbourhood `W` is a member iff every fiber is a
`V`-neighbourhood and all but finitely many fibers equal `Δ`; there is **no deletion/collapse** as in
`⊗`/`⊕`. So it admits the project's *full* `ComputablePresentation` — and **choice-free**.

**Coding.** Given a presentation `P` of `V`, a `D^∞`-code `t : ℕ` codes the finite list of fiber
indices `[i₀, i₁, …, i_{ℓ-1}]` (`Recursive.decodeList`); fiber `j` of the enumerated neighbourhood is
`P.X (iterIdx t j)`, where `iterIdx t j = nthCode t j P.masterIdx` reads the `j`-th list entry,
defaulting to `P.masterIdx` (so all but finitely many fibers are `Δ`). The intersection function is
built by `tabCode`-tabulating `P.inter` coordinate-wise. All three relations and the `inter` function
are primitive recursive because they are bounded computations over `nthCode`/`tabCode`/`P`'s data. -/

section Iterate

open Domain.Recursive

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)



variable {P}














@[simp] theorem iterPresentation_X (t : ℕ) : (iterPresentation P).X t = iterEnum P t := rfl

/-! ### The appropriate combinators: the coordinate projections `projN n` are computable.

Scott's "various appropriate combinators" for `D^∞` are the coordinate projections `projN n`
(Exercise 3.16). Relative to the presentation `iterPresentation P`, the relation
`W (projN n) X ↔ fiber W n ⊆ X` reads off as `X_{iterIdx t n} ⊆ X_b` — a recursive slice of
`incl_computable`, hence r.e. (In particular `head = projN 0`.) -/
end Iterate
end DomainTheory.NeighbourhoodSystems
