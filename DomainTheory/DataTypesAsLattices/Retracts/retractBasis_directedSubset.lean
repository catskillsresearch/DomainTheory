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
public import DomainTheory.DataTypesAsLattices.Retracts.retractBasis_directed

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






































theorem retractBasis_directedSubset {a : Pomega} (ha : IsRetract a)
    (x : Fixpoints (funOf a)) :
    IsDirectedSubset (retractBasis a x) := by
  have h := retractBasis_directed ha x
  refine ⟨h.1, ?_⟩
  intro y hy z hz
  obtain ⟨w, hw, hyw, hzw⟩ := h.2 hy hz
  exact ⟨w, hw, hyw, hzw⟩

end DomainTheory.DataTypesAsLattices
