/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.plus7_app_tag5

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
































theorem plus7_typed_inl5 {a0 a1 a2 a3 a4 a5 a6 x : Pomega} (hx : typed x a5) :
    typed (tagInj 5 x) (plus7 a0 a1 a2 a3 a4 a5 a6) := by
  rw [typed, plus7_app_tag5, ← hx]

end DomainTheory.DataTypesAsLattices
