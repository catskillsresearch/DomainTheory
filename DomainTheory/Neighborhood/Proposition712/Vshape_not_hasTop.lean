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
import DomainTheory.Neighborhood.Proposition712.Vshape_mem_true
import DomainTheory.Neighborhood.Proposition712.Vshape_mem_false
import DomainTheory.Neighborhood.Proposition712.Vshape_not_mem_empty


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive



namespace Counterexample712C

open NeighborhoodSystem

variable {γ δ : Type*}







/-- **`|Vshape|` has no greatest element.** A greatest element would contain both `{true}` and
`{false}`, hence (by `inter_mem`) their intersection `∅`, which is not a neighbourhood. -/
theorem Vshape_not_hasTop : ¬ HasTop Vshape := by
  rintro ⟨t, ht⟩
  have htt : t.mem {true} :=
    ht (Vshape.principal Vshape_mem_true) {true} ⟨Vshape_mem_true, subset_rfl⟩
  have htf : t.mem {false} :=
    ht (Vshape.principal Vshape_mem_false) {false} ⟨Vshape_mem_false, subset_rfl⟩
  have hint : t.mem (({true} : Set Bool) ∩ {false}) := t.inter_mem htt htf
  rw [tf_inter] at hint
  exact Vshape_not_mem_empty (t.sub hint)

end Counterexample712C
end DomainTheory.Neighborhood
