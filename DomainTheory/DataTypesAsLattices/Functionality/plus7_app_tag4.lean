/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.predSet_iterate_ofNat
public import DomainTheory.DataTypesAsLattices.Functionality.predSet_iterate_self
public import DomainTheory.DataTypesAsLattices.Functionality.plus7_app
public import DomainTheory.DataTypesAsLattices.Functionality.tagInj_zero
public import DomainTheory.DataTypesAsLattices.Functionality.tagInj_one

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
































theorem plus7_app_tag4 (a0 a1 a2 a3 a4 a5 a6 x : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) (tagInj 4 x) = tagInj 4 (funOf a4 x) := by
  rw [plus7_app, plus7Body, tagInj_zero, tagInj_one, dcondSet_ofNat_succ,
    predSet_ofNat_succ, dcondSet_ofNat_succ, predSet_ofNat_succ,
    dcondSet_ofNat_succ, predSet_iterate_ofNat (k := 3) (i := 1),
    dcondSet_ofNat_one, predSet_iterate_self, dcondSet_ofNat_zero]

end DomainTheory.DataTypesAsLattices
