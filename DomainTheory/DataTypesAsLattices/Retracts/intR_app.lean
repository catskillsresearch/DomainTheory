/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.FixedLattices
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Retracts.Basic
import DomainTheory.DataTypesAsLattices.Retracts.intF_app
import DomainTheory.DataTypesAsLattices.Retracts.intR_eq_intF


namespace DomainTheory.DataTypesAsLattices














































theorem intR_app (u : Pomega) :
    funOf intR u =
      dcondSet u (ofNat 0) (dcondSet (funOf intR (predSet u)) u u) := by
  have h := congrArg (fun a => funOf a u) intR_eq_intF
  simpa [intF_app] using h.symm

end DomainTheory.DataTypesAsLattices
