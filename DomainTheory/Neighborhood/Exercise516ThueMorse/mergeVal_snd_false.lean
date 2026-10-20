/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise516
import Mathlib.Data.Nat.Bits
import DomainTheory.Neighborhood.Exercise516ThueMorse.Basic


namespace DomainTheory.Neighborhood.Exercise516

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419






/-- The second (total/partial-flag) component of an interleaving with a partial first input is always
`false`: a partial input keeps the output partial. -/
theorem mergeVal_snd_false : ∀ (σ τ : Str) (b₁ : Bool), (mergeVal σ false τ b₁).2 = false
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: σ, _ :: τ, b₁ => by simp only [mergeVal_cons_cons]; exact mergeVal_snd_false σ τ b₁

end DomainTheory.Neighborhood.Exercise516
