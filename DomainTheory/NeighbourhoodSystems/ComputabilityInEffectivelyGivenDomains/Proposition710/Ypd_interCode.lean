/-ai
The neighbourhood coded by the intersection code of n and m equals the intersection of the neighbourhoods coded by n and by m, whenever cons decides whether two enumerated neighbourhoods are consistent.

Rewrite the intersection code by its fold equation, apply the outer-fold identity to the decoded list of n starting from accumulator 0, replace the neighbourhood coded by 0 by the empty set, drop the empty union, and return to the definition of the coded neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.Ypd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.Ypd_def
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.Ypd_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.interCode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.interCode_eq
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.Ypd_outerfoldl

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

variable (P : ComputablePresentation V)

/-- **Correctness of the intersection code:** `Y_{interCode n m} = Y_n ∩ Y_m`. -/
theorem Ypd_interCode (cons : ℕ → ℕ) (n m : ℕ)
    (hcons : ∀ a b, cons (Nat.pair a b) = 1 ↔ ∃ k, P.X k ⊆ P.X a ∩ P.X b) :
    V.Ypd P (V.interCode P cons n m) = V.Ypd P n ∩ V.Ypd P m := by
  rw [V.interCode_eq P, V.Ypd_outerfoldl P cons m hcons (decodeList n) 0, V.Ypd_zero P,
    Set.empty_union, ← V.Ypd_def P]

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
