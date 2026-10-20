/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.FixedLattices
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Retracts.Basic
import DomainTheory.DataTypesAsLattices.Retracts.sSup_fixed_eq_sUnion
import DomainTheory.DataTypesAsLattices.Retracts.retractBasis_directed
import DomainTheory.DataTypesAsLattices.Retracts.retractBasis_sSup


namespace DomainTheory.DataTypesAsLattices






































theorem retractBasis_sUnion {a : Pomega} (ha : IsRetract a)
    (x : Fixpoints (funOf a)) :
    (x : Pomega) = ⋃₀ (Subtype.val '' retractBasis a x) := by
  have h := retractBasis_sSup ha x
  have hsu := sSup_fixed_eq_sUnion (funOf_isScottContinuous a)
    (retractBasis_directed ha x)
  have : (x : Pomega) = (sSup (retractBasis a x) : Fixpoints (funOf a)) :=
    congrArg Subtype.val h
  exact this.trans hsu

end DomainTheory.DataTypesAsLattices
