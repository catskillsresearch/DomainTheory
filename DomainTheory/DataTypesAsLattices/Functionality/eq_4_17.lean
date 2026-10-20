/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_zero
public import DomainTheory.DataTypesAsLattices.Functionality.tensorR_app
public import DomainTheory.DataTypesAsLattices.Functionality.tensorR_isRetract

@[expose] public section


namespace DomainTheory.DataTypesAsLattices















/-- **Scott 1976, (4.17).** `fst ∘ (a ⊗ b) : (a ⊗ b) ∘→ a`. -/
theorem eq_4_17 {a b : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    typed (comp fstC (tensorR a b)) (arrowR (tensorR a b) a) := by
  change comp fstC (tensorR a b) =
    funOf (arrowR (tensorR a b) a) (comp fstC (tensorR a b))
  rw [arrowR_app]
  apply graph_ext
  intro u
  have hab := tensorR_isRetract ha hb
  simp only [comp_app, fstC_app, retract_app hab]
  rw [tensorR_app, pairSeq_app_zero, retract_app ha]

end DomainTheory.DataTypesAsLattices
