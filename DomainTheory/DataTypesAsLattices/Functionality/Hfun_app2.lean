/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.HF_app2
public import DomainTheory.DataTypesAsLattices.Functionality.Hfun_fixed

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
















































theorem Hfun_app2 (e t : Pomega) :
    funOf (funOf Hfun e) t = Hstep Hfun e t := by
  have h := congrArg (fun H => funOf (funOf H e) t) Hfun_fixed
  simpa [HF_app2] using h.symm

end DomainTheory.DataTypesAsLattices
