/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.funOf_isScottContinuous_left
public import DomainTheory.DataTypesAsLattices.Lambda.id_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.const_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


































theorem ofComb_update_isScottContinuous (c : Comb) (ρ : ℕ → Pomega) (i : ℕ) :
    IsScottContinuous (fun v => ofComb c (envSet ρ i v)) := by
  induction c generalizing ρ i with
  | var j =>
    intro x
    by_cases hj : j = i
    · subst hj; simpa [ofComb, envSet, Function.update] using id_isScottContinuous x
    · simpa [ofComb, envSet, Function.update, hj] using const_isScottContinuous (ρ j) x
  | zero => intro x; simpa [ofComb] using const_isScottContinuous zeroC x
  | suc => intro x; simpa [ofComb] using const_isScottContinuous sucC x
  | pred => intro x; simpa [ofComb] using const_isScottContinuous predC x
  | cond => intro x; simpa [ofComb] using const_isScottContinuous condC x
  | K => intro x; simpa [ofComb] using const_isScottContinuous Kcomb x
  | S => intro x; simpa [ofComb] using const_isScottContinuous Scomb x
  | app u v iu iv =>
    exact theorem_1_3_tuple
      (fun y => funOf_isScottContinuous_left y)
      (fun t => funOf_isScottContinuous t)
      (iu ρ i) (iv ρ i)

end DomainTheory.DataTypesAsLattices
