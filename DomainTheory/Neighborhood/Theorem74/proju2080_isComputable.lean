/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Definition72
import DomainTheory.Neighborhood.Exercise319
import DomainTheory.Neighborhood.Exercise319Sum
import DomainTheory.Neighborhood.Theorem74.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ α' β' : Type*}


variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}





/-- **Theorem 7.4 (Scott 1981, PRG-19) — `proj₀` is computable.** `(Xₙ⁰ ∪ Xₘ¹) p₀ X⁰_k ↔ Xₙ⁰ ⊆ X⁰_k`,
a recursive slice of `incl_computable`, hence r.e. -/
theorem proj₀_isComputable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁) :
    IsComputableMap (prodPresentation P₀ P₁) P₀ (proj₀ V₀ V₁) := by
  have hincl : RecDecidable (fun s => P₀.X s.unpair.1 ⊆ P₀.X s.unpair.2) := P₀.incl_computable
  have hr : Nat.Primrec (fun t => Nat.pair t.unpair.1.unpair.1 t.unpair.2) :=
    (Nat.Primrec.left.comp Nat.Primrec.left).pair Nat.Primrec.right
  refine (RecDecidable.of_iff (fun t => ?_) (hincl.comp hr)).re
  simp only [prodPresentation_X, proj₀_rel, inl_preimage_prodNbhd, unpair_pair_fst, unpair_pair_snd]
  exact ⟨fun h => h.2.2,
    fun h => ⟨prod_mem_prodNbhd (P₀.mem_X _) (P₁.mem_X _), P₀.mem_X _, h⟩⟩

end DomainTheory.Neighborhood
