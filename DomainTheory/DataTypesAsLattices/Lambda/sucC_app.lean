/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.succSet_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

































theorem sucC_app (x : Pomega) : funOf sucC x = succSet x :=
  beta succSet_isScottContinuous x

end DomainTheory.DataTypesAsLattices
