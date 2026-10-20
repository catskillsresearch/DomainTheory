/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise722DFA
import DomainTheory.Neighborhood.Exercise722Cat
import DomainTheory.Neighborhood.Exercise722Words
import DomainTheory.Neighborhood.Exercise722Decide.Basic


namespace DomainTheory.Neighborhood

namespace Exercise722

open scoped Computability
open Sum Set

variable {σ₁ σ₂ : Type}














variable {σ : Type}


section ShortWord

variable {σ : Type} [Fintype σ] {M : NFA Bool σ}





omit [Fintype σ] in
theorem pathStateAt_last {s t : σ} {x : List Bool} (p : M.Path s t x) :
    pathStateAt p x.length (Nat.le_refl _) = t := by
  induction p with
  | nil s => simp [pathStateAt, pathStateAtAux]
  | cons sMid s' u a xs hstep p' ih =>
    simp [pathStateAt, pathStateAtAux, List.length_cons]
    exact ih

end ShortWord
end Exercise722
end DomainTheory.Neighborhood
