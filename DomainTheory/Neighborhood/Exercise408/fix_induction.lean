/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.ApproximableExercises
import DomainTheory.Neighborhood.Exercise408.Basic
import DomainTheory.Neighborhood.Exercise408.iterElem_succ
import DomainTheory.Neighborhood.Exercise408.iterElem_zero
import DomainTheory.Neighborhood.Exercise408.iterElem_monotone
import DomainTheory.Neighborhood.Exercise408.fixElement_eq_supChain


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- **Exercise 4.8 (Scott 1981, PRG-19) — fixed-point induction.** If a predicate `P` holds at `⊥`,
is preserved by `f`, and is closed under sups of monotone chains, then it holds at `fix(f)`. -/
theorem fix_induction (f : ApproximableMap V V) (P : V.Element → Prop)
    (hbot : P V.bot)
    (hstep : ∀ x, P x → P (f.toElementMap x))
    (hsup : ∀ (s : ℕ → V.Element) (hmono : Monotone s), (∀ n, P (s n)) → P (supChain s hmono)) :
    P f.fixElement := by
  have hmono : Monotone f.iterElem := iterElem_monotone f
  have hP : ∀ n, P (f.iterElem n) := by
    intro n
    induction n with
    | zero => rw [iterElem_zero]; exact hbot
    | succ k ih => rw [iterElem_succ]; exact hstep _ ih
  rw [fixElement_eq_supChain f]
  exact hsup f.iterElem hmono hP

end ApproximableMap
end DomainTheory.Neighborhood
