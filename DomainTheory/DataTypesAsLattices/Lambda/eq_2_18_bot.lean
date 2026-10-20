/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic


namespace DomainTheory.DataTypesAsLattices


































/-- **Scott 1976, (2.18).** Constants as graphs of constant maps. -/
theorem eq_2_18_bot : botElem = graph (fun _ => botElem) := by
  ext p
  constructor
  · intro hp; exact hp.elim
  · intro hp
    rcases hp with ⟨_, _, _, hm⟩
    simp [botElem] at hm

end DomainTheory.DataTypesAsLattices
