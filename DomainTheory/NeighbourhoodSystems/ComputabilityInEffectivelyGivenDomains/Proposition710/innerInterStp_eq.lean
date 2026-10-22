module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.innerInterStp

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

variable (P : ComputablePresentation V)

theorem innerInterStp_eq (cons : ℕ → ℕ) (a acc b : ℕ) :
    V.innerInterStp P cons (Nat.pair b (Nat.pair acc a))
      = selectFn (isOne (cons (Nat.pair a b))) (Nat.pair (P.inter a b) acc + 1) acc := by
  unfold innerInterStp; simp only [unpair_pair_fst, unpair_pair_snd]

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
