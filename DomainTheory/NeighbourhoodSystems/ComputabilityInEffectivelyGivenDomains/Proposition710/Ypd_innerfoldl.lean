/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.UPX
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.UPX_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.UPX_cons
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.Ypd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.Ypd_innerstep

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

variable (P : ComputablePresentation V)

/-- The inner fold computes `↓X_a ∩ (⋃_{b ∈ bs} ↓X_b)` on top of the starting accumulator. -/
theorem Ypd_innerfoldl (cons : ℕ → ℕ) (a : ℕ)
    (hcons : ∀ b, cons (Nat.pair a b) = 1 ↔ ∃ k, P.X k ⊆ P.X a ∩ P.X b) :
    ∀ (bs : List ℕ) (acc : ℕ),
      V.Ypd P (List.foldl (fun acc b => selectFn (isOne (cons (Nat.pair a b)))
          (Nat.pair (P.inter a b) acc + 1) acc) acc bs)
        = V.Ypd P acc ∪ (V.upSet (P.X a) ∩ V.UPX P bs) := by
  intro bs
  induction bs with
  | nil => intro acc; rw [List.foldl_nil, V.UPX_nil P, Set.inter_empty, Set.union_empty]
  | cons b bs ih =>
    intro acc
    rw [List.foldl_cons, ih, V.Ypd_innerstep P cons (hcons b), V.UPX_cons P,
      Set.inter_union_distrib_left, Set.union_assoc]

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
