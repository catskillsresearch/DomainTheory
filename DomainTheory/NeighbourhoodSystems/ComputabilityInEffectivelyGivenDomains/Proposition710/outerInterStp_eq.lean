/-ai
On the state packed as the pair of a with the pair of the accumulator and m, the outer step equals the inner intersection code of a, the accumulator, and m.

Unfold the definition and simplify the unpairings of the packed pairs.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.innerInterCode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.outerInterStp

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

variable (P : ComputablePresentation V)

theorem outerInterStp_eq (cons : ℕ → ℕ) (a acc m : ℕ) :
    V.outerInterStp P cons (Nat.pair a (Nat.pair acc m)) = V.innerInterCode P cons a acc m := by
  unfold outerInterStp; simp only [unpair_pair_fst, unpair_pair_snd]

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
