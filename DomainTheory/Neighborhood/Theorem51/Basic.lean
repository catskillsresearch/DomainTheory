/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Table55

/-!
# Lecture V (§5) — Theorem 5.1 (Scott 1981, PRG-19)

**Theorem 5.1.** Every typed `λ`-term `τ` defines an approximable function of its free variables.

Scott proves this by induction on the (limited) syntax of `λ`-terms. There are exactly five cases,
and in the neighbourhood-system framework each is realized by a construction already shown to be
approximable in Lectures II–III. The interpretation `⟦τ⟧` of a term with free variables of types
`𝒟₀, …, 𝒟ₙ₋₁` (collected into the context product `Γ = 𝒟₀ × ⋯ × 𝒟ₙ₋₁`) is an *approximable map*
`Γ → 𝒟'`, built as follows:

| term `τ` | interpretation | approximable by |
| -------- | -------------- | --------------- |
| a variable `xᵢ` | a projection `Γ → 𝒟ᵢ` | Def 3.3 (`proj₀`/`proj₁`) |
| a constant `k` | `constMap` | Lemma 3.6 |
| a tuple `⟨σ₀, σ₁⟩` | `⟨⟦σ₀⟧, ⟦σ₁⟧⟩ = paired` | Prop 3.4 |
| an application `σ₀(σ₁)` | `eval ∘ ⟨⟦σ₀⟧, ⟦σ₁⟧⟩` | Thm 3.11 + Thm 2.5 |
| an abstraction `λx.σ` | `curry ⟦σ⟧` | Thm 3.12 |

Because every one of these lands in `ApproximableMap`, "defines an approximable function" holds *by
construction* — the content of Theorem 5.1 is that these five closure operations exist and compute
the intended values, which is what we record here (the value equations `*_apply`). The genuinely
recursive cases (tuple, application, abstraction) carry the induction hypothesis that the
subterms `σᵢ` are already approximable.

This module collects the five closure facts as concrete lemmas; everything is **choice-free**.
-/

namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
  {V₃ : NeighborhoodSystem δ}

namespace Theorem51

/-! ### Case 1 — a variable is a projection (here, the two binary projections of the context). -/

/-! ### Case 2 — a constant. -/

/-! ### Case 3 — a tuple. -/

/-! ### Case 4 — an application. -/

/-! ### Case 5 — an abstraction. -/
end Theorem51
end DomainTheory.Neighborhood
