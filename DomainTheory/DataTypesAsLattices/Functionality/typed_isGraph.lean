/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

















theorem typed_isGraph {a b f : Pomega} (hf : typed f (arrowR a b)) :
    f = graph (fun x => funOf f x) := by
  have hf' := typed_of_arrowR hf
  apply Eq.trans hf'
  apply graph_ext
  intro x
  have : funOf f x = funOf b (funOf f (funOf a x)) := by
    have h1 : funOf f x = funOf (comp b (comp f a)) x :=
      congrArg (fun w => funOf w x) hf'
    rw [h1, comp_app, comp_app]
  rw [comp_app, this]

end DomainTheory.DataTypesAsLattices
