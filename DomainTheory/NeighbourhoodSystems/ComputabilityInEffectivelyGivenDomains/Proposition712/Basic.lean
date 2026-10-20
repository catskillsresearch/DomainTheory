/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition711
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.PDsingletonApproxMap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.PDsingletonMeet
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.PDfinJoinApproxMap₂
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.finJoinMap_prod
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.HasTop
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.improperTop
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.Vshape
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.PDsingleton_mono
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.PDsingletonApproxMap_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.PDsingletonMeet_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.finJoinMap_prod_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.tf_inter
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.ft_inter

@[expose] public section

/-!
# Proposition 7.12 (Scott 1981, PRG-19, §7) — the finite join map on `ℙ𝒟`

Scott states, right after Definition 7.11:

> **Proposition 7.12.** The mapping `λ x₀, …, x_{n-1}. {x₀, …, x_{n-1}} : Dⁿ → ℙD` is approximable
> and is computable if `D` is effectively given. Moreover, the map `λ x. {x}` shows that
> `D ⊴ ℙD`, and we also have `{x₀, …, x_{n-1}} = {x₀} ∩ … ∩ {x_{n-1}}` as an intersection of filters.

This file delivers Parts A, B, and D **in full**. Part C (`D ⊴ ℙD`) turns out to be **false in
general** under the present definition of `ℙ𝒟` (Definition 7.9), and we **formalize a
counterexample** instead — see `Counterexample712C` at the bottom.

## Part A — the singleton map `λ x. {x}` is approximable

Built by Exercise 2.8's `ofMono` from its values on principal inputs `↑X ↦ {↑X}` (`PDsingleton`).
Monotonicity uses that `{↑X'}` is *blunter* than `{↑X}` when `X' ⊆ X`.

On finite elements, `{↑X} = ↑(↓X)` in `ℙ𝒟` (`PDsingleton_principal`): the principal filter of the
down-set token `↓X`.

## Part B — the intersection law `{x, y} = {x} ∩ {y}` (hence the general fold)

Scott's proof on principal inputs `{↑X} ∩ {↑Y} = {↑X, ↑Y}` unfolds to
`↓X ∩ ↓Y = ↑(↓X ∩ ↓Y)` via `upSet_inter`, then to the binary join. The general law
`PDfinJoin_inter` follows by induction on `n`.

## Part C — `D ⊴ ℙD` is FALSE in general (counterexample)

Scott's closing remark "`λ x. {x}` shows `D ⊴ ℙD`" does **not** hold for an arbitrary neighbourhood
system `𝒟` once `ℙ𝒟` is taken to include the **empty union `∅`** (Definition 7.9's `n = 0` case,
`PDmem_empty`). The obstruction is structural:

* `ℙ𝒟` is **unconditionally** closed under intersection (`PDmem_inter`; the empty union always
  supplies the missing consistency witness), so `|ℙ𝒟|` has a **greatest element** — the improper
  filter consisting of *all* `ℙ𝒟`-neighbourhoods (`Counterexample712C.hasTop_of_inter_closed`).
* Any subsystem `D' ◁ ℙ𝒟` inherits that unconditional ∩-closure (`Definition 6.10`'s
  `inter_closed`), so `|D'|` **also** has a greatest element.
* `D ⊴ ℙ𝒟` means `D ≅ᴰ D'` for some `D' ◁ ℙ𝒟`, and `≅ᴰ` is an order-isomorphism of element
  lattices, which transports "has a greatest element" back to `|D|`.

So `D ⊴ ℙ𝒟` forces `|D|` to have a greatest element. But the two-point **flat** domain `Vshape`
(neighbourhoods `Δ = {true, false}`, `{true}`, `{false}`, with `{true} ∩ {false} = ∅ ∉ 𝒟`) has two
incomparable maximal elements and hence **no** greatest element. Therefore
`Vshape ⋬ Vshape.PowerDomain` (`Counterexample712C.vshape_not_trianglelefteq_powerDomain`).

This is exactly the wall the projection-pair route hit: a monotone (approximable) retraction
`ℙ𝒟 → 𝒟` would have to send `⊤_{ℙ𝒟} = ↑∅` to an upper bound of all of `|𝒟|`, i.e. to a greatest
element of `|𝒟|`, which need not exist. Scott's claim is correct precisely when `|𝒟|` has a top
(equivalently `𝒟` has a least neighbourhood), e.g. when `∅ ∈ 𝒟`; the singleton injection itself
(`PDsingletonApproxMap`) is the surviving "one half" of the would-be projection pair.

## Part D — computability when `D` is effectively given

Against `PDPresentation` (Proposition 7.10), the neighbourhood relation for `λ x. {x}` is
`∃ b ∈ dl k, X_n ⊆ X_b` — a bounded `∃` over `P.incl_computable` (`singleton_isComputable`).
The binary join map on `D × D` is obtained from two independent singleton conditions
(`PDfinJoinApproxMap₂_isComputable`); the general `n`-ary case reduces to the intersection law.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-! ### Part A — the singleton approximable map. -/




/-! ### Part B — the intersection law. -/



/-! ### Part B continued — binary approximable join map. -/




/-! ### Part D — computability. -/

variable (P : ComputablePresentation V)

end NeighborhoodSystem

/-! ## Part C — counterexample: `D ⊴ ℙD` fails for the flat two-point domain.

The argument isolates a single domain invariant — *having a greatest element* — that `ℙ𝒟` (with the
empty union) always satisfies but a general `𝒟` need not, and that is preserved under both `◁` and
`≅ᴰ`. -/

namespace Counterexample712C

open NeighborhoodSystem

variable {γ δ : Type*}



/-! ### The flat two-point domain `Vshape`, with no greatest element. -/



end Counterexample712C
end DomainTheory.NeighbourhoodSystems
