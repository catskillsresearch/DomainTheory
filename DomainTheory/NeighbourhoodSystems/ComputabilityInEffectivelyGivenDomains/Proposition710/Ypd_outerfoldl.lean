/-ai
The outer fold of the inner intersection code along a list, with parameter m, returns the union of the accumulator neighbourhood with the intersection of the finite union of down-sets of that list and the neighbourhood coded by m, whenever cons decides consistency.

Induct on the list. On the empty list the fold is the accumulator, the finite union of down-sets is empty, and the empty intersection and the empty union give the claim. On a cons cell, rewrite by the inductive hypothesis and the inner-intersection-code identity at the head, then apply the cons law for the finite union of down-sets and distribute that intersection across the union.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.UPX
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.UPX_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.UPX_cons
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.Ypd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.innerInterCode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.Ypd_innerInterCode

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

variable (P : ComputablePresentation V)

/-- The outer fold computes `(⋃_{a ∈ as} ↓X_a) ∩ Y_m` on top of the starting accumulator. -/
theorem Ypd_outerfoldl (cons : ℕ → ℕ) (m : ℕ)
    (hcons : ∀ a b, cons (Nat.pair a b) = 1 ↔ ∃ k, P.X k ⊆ P.X a ∩ P.X b) :
    ∀ (as : List ℕ) (acc : ℕ),
      V.Ypd P (List.foldl (fun acc a => V.innerInterCode P cons a acc m) acc as)
        = V.Ypd P acc ∪ (V.UPX P as ∩ V.Ypd P m) := by
  intro as
  induction as with
  | nil => intro acc; rw [List.foldl_nil, V.UPX_nil P, Set.empty_inter, Set.union_empty]
  | cons a as ih =>
    intro acc
    rw [List.foldl_cons, ih, V.Ypd_innerInterCode P cons a acc m (hcons a), V.UPX_cons P,
      Set.union_inter_distrib_right, Set.union_assoc]

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
