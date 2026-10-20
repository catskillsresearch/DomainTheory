/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826.Uapply
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826.Ulam
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826.translateAbs

@[expose] public section

/-!
# Exercise 8.26 (Scott 1981, PRG-19) — untyped `λ`-calculus in `𝒰`, and translating typed calculus back

> **Exercise 8.26.** Discuss in more detail the "pay-off" for `𝒰`, namely the translation of
> "untyped" `λ`-calculus into `𝒰` as shown by the equations at the end of the lecture after the
> proof of 8.9. In particular show how the whole of the **typed** `λ`-calculus can be retranslated
> back into `𝒰` with the aid of projections. (Hint: whenever you want to write `f : D_a → D_b`,
> write instead `f = b∘f∘a`, where `a, b` are finitary projections. Whenever you want to form a
> `λ`-abstraction `λx^{D_a}.σ`, where `σ` is of type `D_b`, instead form `λx. b(σ'[a(x)/x])`, where
> `σ'` is the further translation of `σ` into untyped `λ`-calculus. Be sure to show that this
> result "has the right type" in the sense defined above.)

This is a genuinely **expository** exercise ("discuss in more detail"), unlike 8.17–8.25's crisp
existence/uniqueness claims — Scott is asking the reader to *unpack and verify* a translation
scheme he has already sketched, not to discover new mathematics. The formalization below extracts
the three pieces of that scheme that are actually checkable claims, and proves each:

1. **The end-of-lecture equations** (self-hosted application/abstraction): `𝒰` becomes its own
   model of untyped `λ`-calculus once we fix `i_→ : (𝒰→𝒰) → 𝒰`, `j_→ : 𝒰 → (𝒰→𝒰)` (Definition
   8.9). Application of one `𝒰`-element to another is `u(x) := j_→(u)(x)` (`Uapply`); abstraction
   of an "outside" function `f : 𝒰 → 𝒰` is `λx.f ≅ i_→(f)` (`Ulam`). The content beyond bare
   notation is **faithfulness**: the self-hosted calculus computes the same thing as the outside
   one, `Uapply (Ulam f) x = f(x)` (`Uapply_Ulam`) — i.e. `β`-reduction inside `𝒰`'s internal
   `λ`-calculus is sound, using exactly `jArrow_comp_iArrow : j_→∘i_→ = I`.
2. **The hint's translation recipe for `λ`-abstraction, and "has the right type."** Generalizing
   away from `𝒰` to *any* neighbourhood system `E` and *any* retractions `a, b : E → E` (in
   particular finitary projections, Definition 8.3): given the further-translated body
   `body : E → E` (Scott's `σ'`), the recipe `λx. b(σ'[a(x)/x])` is `translateAbs a b body :=
   b∘body∘a`, and it **always** satisfies the defining sandwich equation `f = b∘f∘a`
   (`translateAbs_sandwich`) — this is exactly "has the right type," and needs nothing about
   `body`'s own well-typedness, only idempotence of `a`, `b`. A one-line corollary
   (`translateApp_hasType`) checks the matching claim for **application**: if `f = b∘f∘a` and `x`
   already has type `D_a` (`a(x) = x`), then `f(x)` already has type `D_b` (`b(f(x)) = f(x)`).
3. **The correspondence `f = b∘f∘a` really does capture `D_a → D_b`.** This is *not* new content —
   it is exactly Proposition 8.10(b)'s `arrowComb_elementIso`/`finitaryProjection_arrowComb`
   (`Proposition810b.lean`), which for finitary projections `a, b` produces
   `(D_a → D_b).Element ≃o {f : 𝒰.Element ∣ (a→b)(f) = f}` — i.e. every `g : D_a → D_b` *is*
   (uniquely) some `f` with `f = b∘f∘a`, and conversely. We do not reprove this; we cite it as
   answering the hint's opening sentence directly.

**What is deliberately out of scope.** A full formal syntax + typing judgment for the typed
`λ`-calculus (variables, application, abstraction, a base-type context, substitution, and a
structural induction assembling 1–3 above into "every typed term translates to an untyped one of
the right type") is not built. The reason is the same one already used to defer the *effectiveness*
clauses of Theorem 8.6/Exercise 8.23/Exercise 8.25: this project's convention is to formalize the
mathematical content precisely (here: the two checkable claims 1–2, plus citing 3) while leaving
genuinely open-ended "build a term language and induct over it" scaffolding as prose discussion,
since the payoff — the induction is a routine unfolding of 1–3 at each syntax constructor, with
`+`/`×` cases following `→`'s pattern exactly (`sumComb`/`prodComb`'s own `IsRetraction`/sandwich
facts are already in `Proposition810.lean`/`Proposition810b.lean`, so `translateAbs_sandwich`
applies to *any* of the three combinators, not just `→`) — is not itself a new mathematical
question. Scott's own hint stops at exactly this level of detail ("whenever you want to..."),
i.e. a *recipe*, not a compiler; we formalize the recipe and its correctness.

Axiom audit: `Uapply_Ulam` mentions `𝒰`, hence inherits `𝒰`'s own `Classical.choice` footprint
(⊆ `{propext, Classical.choice, Quot.sound}`, not new). `translateAbs_sandwich`/
`translateApp_hasType` are fully general (no mention of `𝒰`) and **choice-free**
(`⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

/-! ## Part 1 (of the exercise write-up): the end-of-lecture equations, self-hosted in `𝒰` -/



/-! ## Part 2 (of the exercise write-up): the abstraction recipe, and "has the right type" -/

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

end DomainTheory.NeighbourhoodSystems
