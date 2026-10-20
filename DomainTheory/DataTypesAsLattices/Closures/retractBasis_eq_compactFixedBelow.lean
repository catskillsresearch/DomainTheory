/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.IsClosure
public import DomainTheory.DataTypesAsLattices.Closures.closure_expansive
public import DomainTheory.DataTypesAsLattices.Closures.compactFixedBelow

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

theorem retractBasis_eq_compactFixedBelow {a : Pomega} (ha : IsClosure a)
    (x : Fixpoints (funOf a)) :
    retractBasis a x = compactFixedBelow a x := by
  ext k
  constructor
  · rintro ⟨n, hnx, hkn⟩
    refine ⟨⟨n, hkn⟩, ?_⟩
    rw [hkn]
    have := isScottContinuous_monotone (funOf_isScottContinuous a) hnx
    rwa [x.property] at this
  · rintro ⟨⟨n, hkn⟩, hkx⟩
    refine ⟨n, ?_, hkn⟩
    have hsub : funOf a (e n) ⊆ (x : Pomega) := by
      rwa [hkn] at hkx
    exact (closure_expansive ha (e n)).trans hsub

end DomainTheory.DataTypesAsLattices
