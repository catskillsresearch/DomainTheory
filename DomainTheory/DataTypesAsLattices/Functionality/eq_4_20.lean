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

@[expose] public section


namespace DomainTheory.DataTypesAsLattices















/-- **Scott 1976, (4.20).** `fst ∘ (f ⊗ f') = f ∘ fst`. -/
theorem eq_4_20 (f f' : Pomega) :
    comp fstC (tensorR f f') = comp f fstC := by
  simp only [comp]
  apply graph_ext
  intro u
  rw [fstC_app, tensorR_app, pairSeq_app_zero, fstC_app]

end DomainTheory.DataTypesAsLattices
