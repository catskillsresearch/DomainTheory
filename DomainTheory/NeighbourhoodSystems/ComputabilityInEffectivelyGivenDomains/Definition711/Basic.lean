/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition711.PDmemFinJoin
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition711.PDfinJoinZero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition711.PDfinJoinSucc
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition711.PDfinJoin
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition711.PDsingleton
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition711.PDmem_finJoinZero

@[expose] public section

/-!
# Definition 7.11 (Scott 1981, PRG-19, §7) — finite-element joins in `ℙ𝒟`

Scott introduces the power-domain analogue of a *finite set* of elements.

**Definition 7.11.** For elements `x₀, …, x_{n-1} ∈ |𝒟|` define

`{x₀, …, x_{n-1}} = { z ∈ |ℙ𝒟| ∣ ∃ X₀ ∈ x₀ … ∃ X_{n-1} ∈ x_{n-1}.
  ⋃_{i<n} (↑X_i) ⊆ z }`,

where `↑X` is the principal filter of `X ∈ 𝒟`. Scott also notes the equivalent formulation
`∀ i < n. X_i ∈ z` (read with `X_i` identified with the down-set `↓X_i ∈ ℙ𝒟`).

On finite elements `↑X` of `|𝒟|`, `{↑X}` is the principal filter `↑(↓X)` of `ℙ𝒟` (Prop 7.12).

## What this file formalizes

Building on `Proposition710.lean`'s `PowerDomain`, we package Scott's join as a filter
`PDfinJoin xs : V.PowerDomain.Element` for `xs : Fin n → V.Element` (`n = 0` gives `⊥`).

Membership is the down-set form of Scott's union condition:

`W ∈ {x₀,…,x_{n-1}} ↔ ∃ (X_i ∈ x_i). PD.mem W ∧ ∀ i. ↓X_i ⊆ W`,

equivalently `PD.mem W ∧ ⋃_{i<n} ↓X_i ⊆ W` for some choice of representatives. The singleton
`PDsingleton x` is the unary join; on principal filters, `PDsingleton (↑X) = ↑(↓X)`.
-/

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-! ### Definition 7.11 — membership predicate. -/


/-! ### Definition 7.11 — the join element. -/





theorem PDmem_finJoinSucc {m : ℕ} (xs : Fin (m + 1) → V.Element) {W : Set (Set α)} :
    (V.PDfinJoinSucc xs).mem W ↔ V.PDmemFinJoin xs W := Iff.rfl


@[simp] theorem PDmem_singleton {x : V.Element} {W : Set (Set α)} :
    (V.PDsingleton x).mem W ↔
      ∃ X, x.mem X ∧ V.PowerDomain.mem W ∧ V.upSet X ⊆ W := by
  rw [PDsingleton, PDfinJoin, PDmem_finJoinSucc, PDmemFinJoin]
  constructor
  · rintro ⟨X, hX, hPD, hsub⟩
    exact ⟨X 0, hX 0, hPD, hsub 0⟩
  · rintro ⟨X, hX, hPD, hsub⟩
    refine ⟨fun _ => X, fun _ => hX, hPD, fun _ => hsub⟩
end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
