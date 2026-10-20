/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.condSet_bot

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






















theorem condSet_same_bot (x : Pomega) : condSet botElem x x = botElem :=
  condSet_bot x x

end DomainTheory.DataTypesAsLattices
