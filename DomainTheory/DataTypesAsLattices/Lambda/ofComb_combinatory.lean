/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


































theorem ofComb_combinatory (c : Comb) (ρ : ℕ → Pomega)
    (hρ : ∀ i, IsCombinatory (ρ i)) :
    IsCombinatory (ofComb c ρ) := by
  induction c with
  | var i => exact hρ i
  | zero => exact .zero
  | suc => exact .suc
  | pred => exact .pred
  | cond => exact .cond
  | K => exact .K
  | S => exact .S
  | app _ _ iu iv => exact .app iu iv

end DomainTheory.DataTypesAsLattices
