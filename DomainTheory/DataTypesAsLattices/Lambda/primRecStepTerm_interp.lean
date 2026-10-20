/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_2_beta

@[expose] public section


namespace DomainTheory.DataTypesAsLattices























































theorem primRecStepTerm_interp (a f u n : Pomega) :
    funOf (funOf (funOf (funOf (interp primRecStepTerm (fun _ => botElem)) a) f) u) n =
      condSet n a (funOf (funOf f (predSet n)) (funOf u (predSet n))) := by
  change funOf (funOf (funOf (funOf (interp (.lam 0 _) (fun _ => botElem)) a) f) u) n = _
  rw [theorem_2_2_beta]
  rw [theorem_2_2_beta]
  rw [theorem_2_2_beta]
  rw [theorem_2_2_beta]
  simp [interp, envSet, Function.update]

end DomainTheory.DataTypesAsLattices
