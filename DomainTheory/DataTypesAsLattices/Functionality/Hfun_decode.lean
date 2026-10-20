/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.HF_app
public import DomainTheory.DataTypesAsLattices.Functionality.Hfun_fixed
public import DomainTheory.DataTypesAsLattices.Functionality.Hfun_app2
public import DomainTheory.DataTypesAsLattices.Functionality.Hfun_interp

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
















































theorem Hfun_decode (τ : LambTerm) :
    funOf Hfun (encodeExp τ) = graph (Hinterp τ) := by
  have hβ : funOf Hfun (encodeExp τ) = graph (fun t => Hstep Hfun (encodeExp τ) t) := by
    have := congrArg (fun H => funOf H (encodeExp τ)) Hfun_fixed
    simpa [HF_app] using this.symm
  refine hβ.trans ?_
  apply congrArg graph
  funext t
  simpa [Hfun_app2] using Hfun_interp τ t

end DomainTheory.DataTypesAsLattices
