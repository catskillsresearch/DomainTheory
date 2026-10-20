/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.positiveExample
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.a
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.b
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.memSet
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.notPositiveSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.Tok
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.mem_iff
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.mem_master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.mem_a
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.mem_b
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.not_mem_sub_one
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.inter_eq

@[expose] public section

/-!
# Exercise 1.19 (Scott 1981, PRG-19, §1) — positive neighbourhood systems

Scott replaces condition (ii) of Definition 1.1 by the biconditional **(ii′)**: whenever
`X, Y ∈ 𝒟`, then `X ∩ Y ≠ ∅ ⟺ X ∩ Y ∈ 𝒟`. The predicate `IsPositive` and the builder
`ofPositive` (positive ⟹ neighbourhood system) live in `Basic.lean`.

This file supplies the two examples requested by the exercise:

* `positiveExample` — a genuinely *positive* system (all non-empty subsets of `Δ`, built with
  `ofPositive`), with `positiveExample_isPositive`;
* a *non-positive* neighbourhood system `notPositiveSystem` over `Δ = {0,1,2}` with
  `𝒟 = {Δ, {0,1}, {1,2}}`. It satisfies Definition 1.1 (the only overlapping pair `{0,1}`,
  `{1,2}` has intersection `{1}`, which has **no** consistency witness in `𝒟`, so (ii) never
  fires) yet fails (ii′): `{0,1} ∩ {1,2} = {1}` is non-empty but is not a neighbourhood
  (`not_isPositive`). This is a small stand-in for Hoare's `ℕ × ℕ` example (Scott notes
  "smaller examples are of course possible").

Everything is `[propext, Quot.sound]`.
-/

set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

/-! ### A positive system: all non-empty subsets of `Fin 2`. -/


/-! ### A non-positive system over `Δ = {0,1,2}`. -/











end DomainTheory.NeighbourhoodSystems.Exercise119
