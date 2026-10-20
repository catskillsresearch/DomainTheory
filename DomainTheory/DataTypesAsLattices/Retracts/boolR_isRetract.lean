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
public import DomainTheory.DataTypesAsLattices.Retracts.boolR_app
public import DomainTheory.DataTypesAsLattices.Retracts.dcondSet_bool_idem

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


































































theorem boolR_isRetract : IsRetract boolR := by
  apply graph_ext
  intro u
  rw [boolR_app, boolR_app, dcondSet_bool_idem]

end DomainTheory.DataTypesAsLattices
