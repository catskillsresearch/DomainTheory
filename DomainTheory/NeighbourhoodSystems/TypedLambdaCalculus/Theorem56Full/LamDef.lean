/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module


public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Computability.PartrecBasis
import all Mathlib.Computability.PartrecBasis

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Theorem56Full

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)
open DomainTheory.NeighbourhoodSystems.Exercise511 (head tail push)

/-- The universal argument domain `𝒩 = N^∞` (Exercise 3.16). All `k`-ary number functions are
realised as approximable maps `𝒩 → N` depending only on coordinates `0..k-1`. -/
abbrev 𝒩 : NeighborhoodSystem (ℕ × ℕ) := iterSys N

/-- `none ↦ ⊥`, `some n ↦ n̂`. -/
def optElem : Option ℕ → N.Element
  | none => N.bot
  | some n => natElem n

/-- The argument element of `𝒩` whose first `n` coordinates are `optElem (a i)` and the rest `⊥`. -/
def argElem {n : ℕ} (a : Fin n → Option ℕ) : 𝒩.Element :=
  ofSeq (fun i => if h : i < n then optElem (a ⟨i, h⟩) else N.bot)

/-- The argument element of `𝒩` carrying a `List.Vector ℕ n` in its first `n` coordinates. -/
def vecElem {n : ℕ} (v : List.Vector ℕ n) : 𝒩.Element :=
  argElem (fun i => some (v.get i))

/-- A `𝒩`-element is *arg-like* if every coordinate is total or `⊥` (true of all `argElem`). -/
def ArgLike (z : 𝒩.Element) : Prop := ∀ j, component z j = N.bot ∨ ∃ k, component z j = natElem k

/-- `φ : 𝒩 → N` realises the `n`-ary partial function `f` (a *very strict* λ-definition):
`φ` returns `f`'s value on total arguments, `⊥` where `f` is undefined, and `⊥` on *any* arg-like
input with a `⊥` among its first `n` coordinates. -/
structure LamDef {n : ℕ} (φ : ApproximableMap 𝒩 N) (f : List.Vector ℕ n →. ℕ) : Prop where
  defined : ∀ (v : List.Vector ℕ n) (c : ℕ), c ∈ f v → φ.toElementMap (vecElem v) = natElem c
  undef : ∀ (v : List.Vector ℕ n), ¬ (f v).Dom → φ.toElementMap (vecElem v) = N.bot
  strict : ∀ (z : 𝒩.Element), ArgLike z → ∀ i, i < n → component z i = N.bot →
    φ.toElementMap z = N.bot

end DomainTheory.NeighbourhoodSystems.Theorem56Full
