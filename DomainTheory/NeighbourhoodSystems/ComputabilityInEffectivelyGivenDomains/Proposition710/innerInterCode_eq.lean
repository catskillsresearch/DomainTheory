module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.innerInterStp
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.innerInterStp_eq
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.innerInterCode

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

variable (P : ComputablePresentation V)

theorem innerInterCode_eq (cons : ℕ → ℕ) (a acc m : ℕ) :
    V.innerInterCode P cons a acc m
      = List.foldl (fun acc b => selectFn (isOne (cons (Nat.pair a b)))
          (Nat.pair (P.inter a b) acc + 1) acc) acc (decodeList m) := by
  have hf : (fun (acc x : ℕ) => V.innerInterStp P cons (Nat.pair x (Nat.pair acc a)))
      = (fun acc b => selectFn (isOne (cons (Nat.pair a b))) (Nat.pair (P.inter a b) acc + 1) acc) := by
    funext acc b; exact V.innerInterStp_eq P cons a acc b
  unfold innerInterCode; rw [foldCode_eq', hf]

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
