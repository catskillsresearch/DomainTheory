/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_zero
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_app
public import DomainTheory.DataTypesAsLattices.Functionality.funOf_dcondSet

@[expose] public section


namespace DomainTheory.DataTypesAsLattices





















theorem plusR_fst (a b u : Pomega) :
    funOf (funOf (plusR a b) u) (ofNat 0) =
      dcondSet (funOf u (ofNat 0)) (ofNat 0) (ofNat 1) := by
  rw [plusR_app, funOf_dcondSet, pairSeq_app_zero, pairSeq_app_zero]

end DomainTheory.DataTypesAsLattices
