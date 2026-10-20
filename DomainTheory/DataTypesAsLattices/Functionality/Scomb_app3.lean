/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.Scomb_inner_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Functionality.Scomb_app2

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






















theorem Scomb_app3 (f g x : Pomega) :
    funOf (funOf (funOf Scomb f) g) x = funOf (funOf f x) (funOf g x) := by
  rw [Scomb_app2]
  exact beta (Scomb_inner_isScottContinuous f g) x

end DomainTheory.DataTypesAsLattices
