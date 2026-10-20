/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Definition711
import DomainTheory.Neighborhood.Definition72
import DomainTheory.Neighborhood.ApproximableExercises
import DomainTheory.Neighborhood.Product
import DomainTheory.Neighborhood.Proposition710
import DomainTheory.Neighborhood.Theorem74
import DomainTheory.Neighborhood.Lemma615
import Mathlib.Tactic
import DomainTheory.Neighborhood.Proposition712.Basic
import DomainTheory.Neighborhood.Proposition712.PDsingletonApproxMap_rel_Ypd_iff


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)













variable (P : ComputablePresentation V)

/-- **Proposition 7.12 — `λ x. {x}` is computable when `D` is effectively given.** -/
theorem singleton_isComputable (cons : ℕ → ℕ) (hconsp : Nat.Primrec cons)
    (hcons : ∀ a b, cons (Nat.pair a b) = 1 ↔ ∃ k, P.X k ⊆ P.X a ∩ P.X b) :
    IsComputableMap P (V.PDPresentation P cons hconsp hcons) ((PDsingletonApproxMap (V := V))) := by
  have h := P.incl_computable.swap.bExistsList.swap
  refine (RecDecidable.of_iff (fun s => ?_) h).re
  show PDsingletonApproxMap (V := V).rel (P.X s.unpair.1) ((V.PDPresentation P cons hconsp hcons).X s.unpair.2) ↔
      ∃ e ∈ decodeList s.unpair.2, P.X s.unpair.1 ⊆ P.X e
  simp only [PDPresentation]
  apply PDsingletonApproxMap_rel_Ypd_iff (V := V)

end NeighborhoodSystem
end DomainTheory.Neighborhood
