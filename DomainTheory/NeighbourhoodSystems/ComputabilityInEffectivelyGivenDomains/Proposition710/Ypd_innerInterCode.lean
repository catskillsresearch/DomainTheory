/-ai
The enumeration of the inner intersection code of an index, an accumulator, and a code equals the enumeration of the accumulator united with the intersection of the down-set of that index and the enumeration of the code.

Rewrite by the equation for the inner intersection code, the correctness of the inner fold on the decoded list, and the definition of the enumeration.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.Ypd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.Ypd_def
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.innerInterCode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.innerInterCode_eq
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.Ypd_innerfoldl

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

variable (P : ComputablePresentation V)

/-- `Ypd (innerInterCode cons a acc m) = Ypd acc ∪ (↓X_a ∩ Y_m)`. -/
theorem Ypd_innerInterCode (cons : ℕ → ℕ) (a acc m : ℕ)
    (hcons : ∀ b, cons (Nat.pair a b) = 1 ↔ ∃ k, P.X k ⊆ P.X a ∩ P.X b) :
    V.Ypd P (V.innerInterCode P cons a acc m)
      = V.Ypd P acc ∪ (V.upSet (P.X a) ∩ V.Ypd P m) := by
  rw [V.innerInterCode_eq P, V.Ypd_innerfoldl P cons a hcons (decodeList m) acc, ← V.Ypd_def P]

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
