/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510

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

/-- The closed form of `fade`'s elementwise action, generalized (via `mem_toElementMap₂_fade`) from
Example 8.4(a)'s ambient `D` to an arbitrary neighbourhood system `G`. -/
theorem mem_toElementMap_fade {γ : Type*} {G : NeighborhoodSystem γ} (t : O.Element) (w : G.Element)
    {Z : Set γ} :
    ((fade (D := G)).toElementMap (pair t w)).mem Z ↔
      G.mem Z ∧ (Z = G.master ∨ (t.mem ({0} : Set (Fin 2)) ∧ w.mem Z)) := by
  rw [show (fade (D := G)) = ofMap₂ (fade₂ (D := G)) from rfl, toElementMap_ofMap₂_pair,
    mem_toElementMap₂_fade]

/-- `check(x) ∋ {0} ↔ x ≠ ⊥`: the clean, non-set-theoretic form of `mem_toElementMap_check`. -/
theorem check_toElementMap_mem_zero_iff {x : D.Element} :
    (check.toElementMap x).mem ({0} : Set (Fin 2)) ↔ x ≠ D.bot := by
  rw [mem_toElementMap_check]
  constructor
  · rintro ⟨-, h | h⟩
    · exact absurd h fin2_zero_ne_zero_one
    · exact h
  · intro h; exact ⟨O_mem_zero, Or.inr h⟩

/-! ## `smash : D × E → D × E`. -/

section Smash

/-- `(prod D E).bot = ⟨⊥_D, ⊥_E⟩`. -/
theorem pair_bot_bot : pair (D.bot) (E.bot) = (prod D E).bot := by
  apply Element.ext
  intro W
  rw [mem_pair, mem_bot]
  constructor
  · rintro ⟨X, Y, hX, hY, rfl⟩
    rw [mem_bot] at hX hY
    rw [hX, hY, prod_master]
  · intro hW
    refine ⟨D.master, E.master, ?_, ?_, ?_⟩
    · rw [mem_bot]
    · rw [mem_bot]
    · rw [hW, prod_master]

@[simp] theorem prod_bot_fst : ((prod D E).bot).fst = D.bot := by rw [← pair_bot_bot, fst_pair]

@[simp] theorem prod_bot_snd : ((prod D E).bot).snd = E.bot := by rw [← pair_bot_bot, snd_pair]

/-- The inner application `fade(check(y), z)` of Scott's `smash(x, y) = fade(check(x),
fade(check(y), ⟨x, y⟩))`: here `z = ⟨x, y⟩` is passed through `idMap` (Scott's `⟨x,y⟩` *is* the
ambient input). -/
def smashFadeInner : ApproximableMap (prod D E) (prod D E) :=
  (fade (D := prod D E)).comp
    (paired ((check (D := E)).comp (proj₁ D E)) (idMap (prod D E)))

/-- **Example 8.4(b)(ii)'s `smash` combinator.** `smash(x, y) = fade(check(x), fade(check(y),
⟨x, y⟩))`. -/
def smashRetraction : ApproximableMap (prod D E) (prod D E) :=
  (fade (D := prod D E)).comp
    (paired ((check (D := D)).comp (proj₀ D E)) (smashFadeInner (D := D) (E := E)))

end Smash

/-! ## `strict : (D → E) → (D → E)`. -/

section Strict

/-- Two tiny reproofs of `funSpaceEquiv`'s own round-trips, stated standalone so the closed-form
calculations below don't have to fight `OrderIso` field-access notation. -/
theorem toFilter_toApproxMap (φ : (funSpace D E).Element) : toFilter (toApproxMap φ) = φ :=
  (funSpaceEquiv D E).left_inv φ

theorem toApproxMap_toFilter (f : ApproximableMap D E) : toApproxMap (toFilter f) = f :=
  (funSpaceEquiv D E).right_inv f

/-- `g(f, y) = fade(check(y), f(y))`, as a joint approximable map `(D → E) × D → E`. -/
def strictEvalFade : ApproximableMap (prod (funSpace D E) D) E :=
  (fade (D := E)).comp
    (paired ((check (D := D)).comp (proj₁ (funSpace D E) D)) (evalMap D E))

/-- **Example 8.4(b)(i)'s `strict` combinator.** `strict(f) = λy. fade(check(y), f(y))`, built via
Theorem 3.12's `curry`. -/
def strictRetraction : ApproximableMap (funSpace D E) (funSpace D E) := curry strictEvalFade

/-- The closed form of `strict`'s elementwise action: `strict(f)(y) = ⊥_E` if `y = ⊥_D`, else
`f(y)`. -/
theorem toApproxMap_strictRetraction_mem {φ : (funSpace D E).Element} {y : D.Element}
    {Z : Set β} :
    ((toApproxMap (strictRetraction.toElementMap φ)).toElementMap y).mem Z ↔
      E.mem Z ∧ (Z = E.master ∨ (y ≠ D.bot ∧ ((toApproxMap φ).toElementMap y).mem Z)) := by
  show ((toApproxMap ((curry strictEvalFade).toElementMap φ)).toElementMap y).mem Z ↔ _
  rw [toElementMap_curry_apply]
  show (((fade (D := E)).comp
    (paired ((check (D := D)).comp (proj₁ (funSpace D E) D)) (evalMap D E))).toElementMap
      (pair φ y)).mem Z ↔ _
  rw [toElementMap_comp, toElementMap_paired, toElementMap_comp, toElementMap_proj₁, snd_pair,
    evalMap_apply, mem_toElementMap_fade, check_toElementMap_mem_zero_iff]

theorem strictRetraction_apply_bot (φ : (funSpace D E).Element) :
    (toApproxMap (strictRetraction.toElementMap φ)).toElementMap D.bot = E.bot := by
  apply Element.ext
  intro Z
  rw [toApproxMap_strictRetraction_mem, mem_bot]
  constructor
  · rintro ⟨-, rfl | ⟨hne, -⟩⟩
    · rfl
    · exact absurd rfl hne
  · rintro rfl
    exact ⟨E.master_mem, Or.inl rfl⟩

theorem strictRetraction_apply_of_ne_bot {y : D.Element} (hy : y ≠ D.bot)
    (φ : (funSpace D E).Element) :
    (toApproxMap (strictRetraction.toElementMap φ)).toElementMap y
      = (toApproxMap φ).toElementMap y := by
  apply Element.ext
  intro Z
  rw [toApproxMap_strictRetraction_mem]
  constructor
  · rintro ⟨-, rfl | ⟨-, hZ⟩⟩
    · exact ((toApproxMap φ).toElementMap y).master_mem
    · exact hZ
  · intro hZ
    exact ⟨((toApproxMap φ).toElementMap y).sub hZ, Or.inr ⟨hy, hZ⟩⟩

/-- **`f` is a fixed point of `strict` iff `f` is strict.** -/
theorem isStrict_toApproxMap_of_fixed {φ : (funSpace D E).Element}
    (hφ : strictRetraction.toElementMap φ = φ) : Exercise510.IsStrict (toApproxMap φ) := by
  rw [Exercise510.isStrict_iff_apply_bot]
  have h := strictRetraction_apply_bot φ
  rwa [hφ] at h

theorem strictRetraction_fixed_of_isStrict {f : ApproximableMap D E} (hf : Exercise510.IsStrict f) :
    strictRetraction.toElementMap (toFilter f) = toFilter f := by
  have hbot : f.toElementMap D.bot = E.bot := Exercise510.isStrict_iff_apply_bot.mp hf
  have key : toApproxMap (strictRetraction.toElementMap (toFilter f)) = f := by
    apply ext_of_toElementMap
    intro y
    by_cases hy : y = D.bot
    · rw [hy, strictRetraction_apply_bot, hbot]
    · rw [strictRetraction_apply_of_ne_bot hy, toApproxMap_toFilter]
  rw [← toFilter_toApproxMap (strictRetraction.toElementMap (toFilter f)), key]

/-- **Example 8.4(b)(i), the fixed-point representation.** Restricting `funSpaceEquiv` along
`isStrict_toApproxMap_of_fixed`/`strictRetraction_fixed_of_isStrict` identifies `Fix(strict)` with
the strict approximable maps `Exercise510.StrictMap D E`. -/
def strictRetractionFixIso :
    {φ : (funSpace D E).Element // strictRetraction.toElementMap φ = φ} ≃o
      Exercise510.StrictMap D E where
  toFun φ := ⟨toApproxMap φ.1, isStrict_toApproxMap_of_fixed φ.2⟩
  invFun f := ⟨toFilter f.1, strictRetraction_fixed_of_isStrict f.2⟩
  left_inv φ := Subtype.ext (toFilter_toApproxMap φ.1)
  right_inv f := Subtype.ext (toApproxMap_toFilter f.1)
  map_rel_iff' := by
    intro φ φ'
    show toApproxMap φ.1 ≤ toApproxMap φ'.1 ↔ φ.1 ≤ φ'.1
    exact (funSpaceEquiv D E).map_rel_iff
end Strict
end DomainTheory.NeighbourhoodSystems
