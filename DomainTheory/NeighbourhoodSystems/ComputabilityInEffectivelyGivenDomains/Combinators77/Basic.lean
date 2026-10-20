/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Combinators77.inSharpMap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Combinators77.proj0Map
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Combinators77.dsharpPresentation_X
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Combinators77.inSharpMap_rel

@[expose] public section

/-!
# Proposition 7.7 — Milestone 4: the Example 6.1 combinators are computable

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19, Lecture VII.

> **Proposition 7.7.** For any effectively given domain `D`, the domain `D^§` is also effectively
> given, and all the combinators of Example 6.1 prove to be computable.

The "`D^§` is effectively given" half is `Proposition77.dsharp_isEffectivelyGiven`. Here we treat,
as Scott does, *a selection* of the Example 6.1 combinators and exhibit them as
`ApproximableMap`s that are `IsComputableMap` with respect to the canonical presentation
`dsharpPresentation P hD`:

* **`inSharpMap`** — Scott's injection `λx. x^§ : D → D^§` (Example 6.1's `inSharp`). Its
  neighbourhood relation is `X (λx.x^§) W ↔ 0·X ⊆ W`, i.e. `V_{2n+1} ⊆ V_k`, a recursive slice of
  the inclusion decider, hence r.e. (`inSharp_isComputable`). `inSharpMap_toElementMap` checks the
  approximable map really computes `inSharp`.
* **`proj0Map`** — the first projection `D^§ → D^§` of the pair part (so `proj0(⟨x,y⟩^§) = x`,
  `proj0_toElementMap_pairSharp`). Its relation is `W proj₀ Z ↔ Z = Γ ∨ ∃ P Q, W = 1·P ∪ 2·Q ∧
  P ⊆ Z`, i.e. on indices `V_m proj₀ V_k ↔ k = 0 ∨ (m even, m ≠ 0, V_{p(m/2-1)} ⊆ V_k)`. Both
  disjuncts are recursively decidable, hence r.e. (`proj0_isComputable`).

Each combinator's relation is *recursively decidable* (no unbounded search), so computability is
`RecDecidable.re` of a Boolean combination of the inclusion/equality/parity deciders — exactly the
style of Theorem 7.4's `proj₀`/`in₀`. The `ApproximableMap` data is choice-free; only the `Prop`
correctness proofs route through `Classical` (set equality over an arbitrary carrier).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)


/-! ### `λx. x^§ : D → D^§` (Example 6.1's `inSharp`). -/



/-! ### `proj₀ : D^§ → D^§` (first projection of the pair part). -/


@[simp] theorem proj0Map_rel {W Z : Set (List Bool × α)} :
    (proj0Map hD).rel W Z ↔
      MemS D W ∧ MemS D Z ∧ (Z = Gamma D ∨ ∃ Pp Qq, W = embPair Pp Qq ∧ Pp ⊆ Z) := Iff.rfl
end Proposition77
end DomainTheory.NeighbourhoodSystems
