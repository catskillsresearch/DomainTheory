/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise813b
import Mathlib.Topology.Constructions
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Clopen
import DomainTheory.Neighborhood.Exercise813c.Basic


namespace DomainTheory.Neighborhood



















theorem Corresponds.unique_right {X : Set ℕ} {Y₁ Y₂ : Set (ℕ → Bool)}
    (h1 : Corresponds X Y₁) (h2 : Corresponds X Y₂) : Y₁ = Y₂ := by
  obtain ⟨φ, hφX, hφY⟩ := h1
  obtain ⟨ψ, hψX, hψY⟩ := h2
  have hse : SemanticEquiv φ ψ := semanticEquiv_iff_evalSet_eq.mpr (hφX.trans hψX.symm)
  rw [← hφY, ← hψY, semanticEquiv_iff_evalSet'_eq.mp hse]

end DomainTheory.Neighborhood
