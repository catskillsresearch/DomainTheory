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

















theorem comp_isGraph (u v : Pomega) :
    comp u v = graph (fun x => funOf (comp u v) x) := by
  apply graph_ext
  intro x
  exact (comp_app u v x).symm

end DomainTheory.DataTypesAsLattices
