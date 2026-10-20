/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.Ycomb_app
public import DomainTheory.DataTypesAsLattices.Lambda.omega_first_recursion

@[expose] public section


namespace DomainTheory.DataTypesAsLattices























/-- **Scott 1976, Theorem 2.5 (The first recursion theorem).**
If `u` is the graph of a continuous `f`, then `Y(u) = fix(f)`. -/
theorem theorem_2_5 {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    funOf Ycomb (graph f) = fix f := by
  rw [Ycomb_app]
  exact omega_first_recursion hf

end DomainTheory.DataTypesAsLattices
