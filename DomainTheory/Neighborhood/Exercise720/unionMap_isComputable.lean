/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Proposition710
import DomainTheory.Neighborhood.Definition72
import DomainTheory.Neighborhood.Exercise719
import DomainTheory.Neighborhood.Exercise720.Basic
import DomainTheory.Neighborhood.Exercise720.unionMap_rel_Ypd_iff


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*}




/-- **Exercise 7.20 (Scott's first question) — `union` is computable.** Given `P : Computable
Presentation 𝒟` with a primitive-recursive consistency decider `consV`, `union` is a computable map
between the canonical presentations of `ℙℙ𝒟` and `ℙ𝒟` (Proposition 7.10). The inner consistency
decider of `ℙ𝒟` (needed to build the `ℙℙ𝒟` presentation) is the constant decider `fun _ => 1`,
correct because the empty union (`code 0`, `Y₀ = ∅`) lies below every `ℙ𝒟`-neighbourhood. The
relation is in fact recursively *decidable* (a nested bounded `∀∀∃` over `P.incl_computable`). -/
theorem unionMap_isComputable {V : NeighborhoodSystem α} (P : ComputablePresentation V)
    (consV : ℕ → ℕ) (hconsVp : Nat.Primrec consV)
    (hconsVs : ∀ a b, consV (Nat.pair a b) = 1 ↔ ∃ k, P.X k ⊆ P.X a ∩ P.X b) :
    IsComputableMap
      (V.PowerDomain.PDPresentation (V.PDPresentation P consV hconsVp hconsVs)
        (fun _ => 1) (Nat.Primrec.const 1)
        (fun a b => ⟨fun _ => ⟨0, by
            show V.Ypd P 0 ⊆ _
            rw [V.Ypd_zero P]; exact Set.empty_subset _⟩,
          fun _ => rfl⟩))
      (V.PDPresentation P consV hconsVp hconsVs)
      (unionMap V) := by
  have hrd : RecDecidable₂ (fun n m => ∀ c ∈ decodeList n, ∀ a ∈ decodeList c,
      ∃ b ∈ decodeList m, P.X a ⊆ P.X b) := (V.subCode_computable P).bForallList
  have key : RecDecidable₂ (fun n m => (unionMap V).rel
      (V.PowerDomain.Ypd (V.PDPresentation P consV hconsVp hconsVs) n) (V.Ypd P m)) := by
    refine RecDecidable.of_iff (fun t => ?_) hrd
    exact unionMap_rel_Ypd_iff P (V.PDPresentation P consV hconsVp hconsVs) (fun _ => rfl)
  exact key.re

end DomainTheory.Neighborhood
