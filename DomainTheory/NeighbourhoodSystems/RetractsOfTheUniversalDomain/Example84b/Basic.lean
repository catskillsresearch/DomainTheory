module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.smashFadeInner
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.smashRetraction
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.strictEvalFade
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.strictRetraction
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.strictRetractionFixIso
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.mem_toElementMap_fade
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.check_toElementMap_mem_zero_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.pair_bot_bot
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.prod_bot_fst
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.prod_bot_snd
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.toFilter_toApproxMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.toApproxMap_toFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.toApproxMap_strictRetraction_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.strictRetraction_apply_bot
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.strictRetraction_apply_of_ne_bot
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.isStrict_toApproxMap_of_fixed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.strictRetraction_fixed_of_isStrict

@[expose] public section

/-!
# Lecture VIII — Example 8.4(b) (Scott 1981, PRG-19): `smash` and `strict` as projections

The remainder of Scott's **EXAMPLES 8.4**, building on Example 8.4(a)'s `check`/`fade` combinators
(`DomainTheory.NeighbourhoodSystems/Neighborhood/Example84.lean`):

* **`smash : D × E → D × E`**, `smash(x, y) = fade(check(x), fade(check(y), ⟨x, y⟩))`, is a
  *projection* on `D × E` whose range is isomorphic to the smash product `D ⊗ E` (Exercise 5.10).
* **`strict : (D → E) → (D → E)`**, `strict(f) = λx. fade(check(x), f(x))`, is a *projection* on
  the function space `(D → E)` whose range is isomorphic to the strict function space `D →⊥ E`
  (Exercise 5.10).

## Formalization strategy

Both combinators reuse `check`/`fade` **verbatim** (they are already generic over the ambient
codomain of `fade` and the ambient domain of `check`), reinstantiated at a second neighbourhood
system: `fade (D := prod D E)`/`fade (D := E)` and `check (D := D)`/`check (D := E)`. No new
`ApproximableMap`-level combinator is built from scratch; the whole file is `comp`/`paired`/`proj`
bookkeeping plus the accompanying closed-form calculations, exactly as in 8.4(a).

**`smash`.** The key move is *reduction to Proposition 8.2*: `Exercise510.smash D E`
(the smash-product neighbourhood system) is a genuine *subsystem* of `prod D E`
(`smash_subsystem_prod`) — every smash neighbourhood is a product neighbourhood, and a proper
smash neighbourhood stays proper (hence still a smash neighbourhood) after any intersection that
lands back inside `prod D E` (`Exercise510.inter_ne_master_left/right` do the heavy lifting,
exactly as in `Exercise510.smash`'s own closure proof). Scott's literal combinator is built first
and its closed form derived directly (`smashRetraction_mem_iff` — literally "leave `z` alone if
neither coordinate is `⊥`, else collapse to `⊥`"); it is then identified with
`Subsystem.retractionOfSubsystem smash_subsystem_prod` (`smashRetraction_eq_retractionOfSubsystem`,
the one genuinely new argument — a "compactness" calculation packing a witness neighbourhood of the
smash out of any pair of non-`⊥` witnesses via `z.fst`/`z.snd` filter algebra), after which
`IsProjection`/`IsFinitary`/the isomorphism to `Exercise510.smash D E` are *all* inherited for free
from Definition 8.3's `Subsystem` corollaries.

**`strict`.** Built directly as `curry (fade.comp (paired (check.comp proj₁) evalMap))` using
Theorem 3.12's `curry`/`evalMap` (no new function-space machinery needed — `curry` already exists).
Its closed form (`toApproxMap_strictRetraction_apply`) says exactly "`strict(f)(y) = ⊥_E` if
`y = ⊥_D`, else `f(y)`", from which: (a) `f` is a fixed point of `strict` iff `f(⊥) = ⊥`, i.e. iff
`IsStrict f` (`strictRetraction_fixed_iff`); (b) restricting `funSpaceEquiv` along this
correspondence gives `Fix(strict) ≃o {f ∣ IsStrict f} = StrictMap D E` (`strictRetractionFixIso`),
which composed with `Exercise510.strictFunEquiv.symm` gives the isomorphism to
`Exercise510.strictFun D E` announced by Scott.

Everything is **choice-free** in the *data* (`smashRetraction`, `strictRetraction`); the packaged
`OrderIso`s and the `IsRetraction`/`IsProjection` *proofs* pick up `Classical.choice` only through
`by_contra`/`by_cases` case splits, exactly mirroring 8.4(a)'s discipline.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-! ## A shared closed form for `fade` at a general codomain. -/



/-! ## `smash : D × E → D × E`. -/

section Smash






end Smash

/-! ## `strict : (D → E) → (D → E)`. -/

section Strict










end Strict
end DomainTheory.NeighbourhoodSystems
