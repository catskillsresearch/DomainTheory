/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR_app
public import DomainTheory.DataTypesAsLattices.Retracts.typed_of_arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.eq_4_11_comp

@[expose] public section


namespace DomainTheory.DataTypesAsLattices









































theorem arrowR_functor {a b a' b' f f' : Pomega}
    (hf : typed f (arrowR a b)) (hf' : typed f' (arrowR a' b')) :
    typed (arrowR f f') (arrowR (arrowR b a') (arrowR a b')) := by
  change arrowR f f' =
    funOf (arrowR (arrowR b a') (arrowR a b')) (arrowR f f')
  rw [arrowR_app]
  have inner := eq_4_11_comp f f' b a'
  have outer := eq_4_11_comp a b' (comp b f) (comp f' a')
  have hf1 := typed_of_arrowR hf
  have hf2 := typed_of_arrowR hf'
  apply Eq.symm
  calc
    comp (arrowR a b') (comp (arrowR f f') (arrowR b a'))
        = comp (arrowR a b') (arrowR (comp b f) (comp f' a')) := by rw [inner]
    _ = arrowR (comp (comp b f) a) (comp b' (comp f' a')) := outer
    _ = arrowR f f' := by
      apply graph_ext
      intro u
      apply graph_ext
      intro x
      have hfx : funOf f x = funOf b (funOf f (funOf a x)) := by
        simpa [comp_app] using congrArg (fun w => funOf w x) hf1
      have hf'y : ∀ y, funOf f' y = funOf b' (funOf f' (funOf a' y)) := by
        intro y
        simpa [comp_app] using congrArg (fun w => funOf w y) hf2
      simp only [comp_app]
      rw [hfx]
      exact (hf'y _).symm

end DomainTheory.DataTypesAsLattices
