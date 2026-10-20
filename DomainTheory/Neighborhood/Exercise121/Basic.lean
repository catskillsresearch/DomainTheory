/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem110

/-!
# Exercise 1.21 (Scott 1981, PRG-19, §1) — Theorem 1.10 in greater detail

Scott asks to work out the proof of Theorem 1.10 more fully and to observe two further
properties of the element-token system `{[X]}` over `|𝒟|`:

* it is **positive** (`tokenSystem_isPositive`), giving "in a different way the same kind of
  conclusion as in 1.20";
* it is **complete** (`tokenSystem_complete`): every filter is *fixed* by a unique point — the
  point whose filter of containing neighbourhoods it is. We formalize "fixed by a point" as
  `IsComplete`, and derive it from the bijection `tokenIso` of Theorem 1.10
  (`tokenSystem_toToken_bijective`). Thus tokens and (partial) elements are identified.

Finally, consistency of `{Xᵢ ∣ i < n}` is equivalent to
`⋂_{i<n} [Xᵢ] ≠ ∅` (`consistent_iff_iInter_bracket_nonempty`), the finite generalization of
Theorem 1.10(2) via Theorem 1.1c.

Everything is `[propext, Quot.sound]` (the corollaries inherit the constructive proofs of
Theorem 1.10 / Theorem 1.1c).
-/

namespace DomainTheory.Neighborhood

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-! ### Completeness: every filter is fixed by a unique point. -/

/-- A neighbourhood system `𝒟'` over `β` is **complete** when every filter `y ∈ |𝒟'|` is *fixed
by a unique point* `b ∈ β`: a neighbourhood `S` lies in `y` iff `b ∈ S`. (Scott: "*a filter is
fixed by a point iff it is the filter of all neighbourhoods containing that point*".) -/
def IsComplete {β : Type*} (V' : NeighborhoodSystem β) : Prop :=
  ∀ y : V'.Element, ∃! b : β, ∀ S, V'.mem S → (y.mem S ↔ b ∈ S)

/-- The filter of `{[X]}` *fixed by* the point `x ∈ |𝒟|` is `toToken x` (the filter of all
brackets containing `x`). By Theorem 1.10 this is a bijection `|𝒟| ≃ |{[X]}|`, so tokens and
(partial) elements are identified. -/
def filterFixedBy (x : V.Element) : V.tokenSystem.Element := V.toToken x

/-! ### Consistency ⟺ non-empty intersection of brackets. -/
end NeighborhoodSystem
end DomainTheory.Neighborhood
