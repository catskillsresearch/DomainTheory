/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb_beta2
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb_beta2

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


































theorem SKK_eq_I : funOf (funOf Scomb Kcomb) Kcomb = graph (fun x => x) := by
  rw [Scomb_beta2]
  apply congrArg graph
  funext x
  simp [Kcomb_beta2]


end DomainTheory.DataTypesAsLattices
