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
public import DomainTheory.DataTypesAsLattices.Retracts.intR_app
public import DomainTheory.DataTypesAsLattices.Retracts.dcondSet_same_ofNat

@[expose] public section


namespace DomainTheory.DataTypesAsLattices














































/-- **Scott 1976, after (4.7).** `int({n}) = {n}`. -/
theorem intR_ofNat : ∀ n, funOf intR (ofNat n) = ofNat n
  | 0 => by
    rw [intR_app, dcondSet_ofNat_zero]
  | n + 1 => by
    rw [intR_app, predSet_ofNat_succ, intR_ofNat n, dcondSet_same_ofNat,
      dcondSet_ofNat_succ]

end DomainTheory.DataTypesAsLattices
