/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic


namespace DomainTheory.DataTypesAsLattices






















theorem theorem_7_2_ii_of_typed {a b f : Pomega} (hf : typed f (arrowR a b)) :
    (arrowE (Ea a) (Ea b)).mem f := by
  have hf' : f = comp b (comp f a) := by
    simpa [typed, arrowR_app] using hf
  have hgraph : f = graph (fun x => funOf f x) := by
    apply Eq.trans hf'
    apply graph_ext
    intro x
    have : funOf f x = funOf b (funOf f (funOf a x)) := by
      have h1 : funOf f x = funOf (comp b (comp f a)) x :=
        congrArg (fun w => funOf w x) hf'
      rw [h1, comp_app, comp_app]
    rw [comp_app, this]
  refine ⟨hgraph, hgraph, ?_⟩
  intro x y hxy
  rcases hxy with ⟨hx, hy, rfl⟩
  have hfx : typed (funOf f x) b := theorem_4_3_ii hf hx
  exact ⟨hfx, hfx, rfl⟩

end DomainTheory.DataTypesAsLattices
