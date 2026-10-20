/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Example43
import DomainTheory.Neighborhood.Exercise326
import DomainTheory.Neighborhood.Exercise511
import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.ApproximableExercises
import Mathlib.Computability.PartrecBasis
import DomainTheory.Neighborhood.Theorem56Full.Basic
import DomainTheory.Neighborhood.Theorem56Full.lamDef_comp
import DomainTheory.Neighborhood.Theorem56Full.primrec_lamDef
import DomainTheory.Neighborhood.Theorem56Full.lamDef_rfind


namespace DomainTheory.Neighborhood.Theorem56Full

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap
open DomainTheory.Neighborhood.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.Neighborhood.Exercise326 (cond)
open DomainTheory.Neighborhood.Exercise511 (head tail push)


























/-- **Theorem 5.6 (Scott 1981, PRG-19) — every partial recursive function is λ-definable.** For each
`Nat.Partrec'` function `f : Vector ℕ n →. ℕ` there is an approximable map `φ : 𝒩 → N` that is a
*very strict* λ-definition of `f`: it returns `f`'s value on total arguments, `⊥` where `f` is
undefined, and `⊥` on any arg-like input with a `⊥` among its first `n` coordinates. -/
theorem partrec_lamDef {n : ℕ} {f : List.Vector ℕ n →. ℕ} (h : Nat.Partrec' f) :
    ∃ φ : ApproximableMap 𝒩 N, LamDef φ f := by
  induction h with
  | prim hp => exact primrec_lamDef hp
  | comp g _ _ ihf ihg =>
      obtain ⟨φf, hφf⟩ := ihf
      choose φg hφg using ihg
      exact ⟨_, lamDef_comp _ g φf hφf φg hφg⟩
  | rfind _ ih =>
      obtain ⟨φf, hφf⟩ := ih
      exact ⟨_, lamDef_rfind φf hφf⟩

end DomainTheory.Neighborhood.Theorem56Full
