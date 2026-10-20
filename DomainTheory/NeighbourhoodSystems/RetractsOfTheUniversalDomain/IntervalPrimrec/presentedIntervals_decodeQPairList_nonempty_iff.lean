/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.mem_decodeQPairList
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.qpNonemptyChar_eq_one_iff

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive








































/-- **`presentedIntervals (decodeQPairList c)` is non-empty iff `qpNonemptyChar c = 1`.** -/
theorem presentedIntervals_decodeQPairList_nonempty_iff (c : ℕ) :
    (presentedIntervals (decodeQPairList c)).Nonempty ↔ qpNonemptyChar c = 1 := by
  rw [presentedIntervals_nonempty_iff, qpNonemptyChar_eq_one_iff]
  constructor
  · rintro ⟨p, hp, hlt⟩
    obtain ⟨e, he, rfl⟩ := (mem_decodeQPairList c p).mp hp
    exact ⟨e, he, hlt⟩
  · rintro ⟨e, he, hlt⟩
    exact ⟨decodeRatPair e, (mem_decodeQPairList c (decodeRatPair e)).mpr ⟨e, he, rfl⟩, hlt⟩

end DomainTheory.NeighbourhoodSystems
