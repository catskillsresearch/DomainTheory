/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb_mid_cont
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb_beta

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

































theorem Scomb_beta2 (f g : Pomega) :
    funOf (funOf Scomb f) g =
      graph (fun x => funOf (funOf f x) (funOf g x)) := by
  rw [Scomb_beta]
  exact beta (Scomb_mid_cont f) g

end DomainTheory.DataTypesAsLattices
