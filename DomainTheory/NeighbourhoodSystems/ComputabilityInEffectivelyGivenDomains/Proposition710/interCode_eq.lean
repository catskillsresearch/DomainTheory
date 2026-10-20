module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.innerInterCode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.outerInterStp
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.outerInterStp_eq
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.interCode

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

variable (P : ComputablePresentation V)

theorem interCode_eq (cons : ℕ → ℕ) (n m : ℕ) :
    V.interCode P cons n m
      = List.foldl (fun acc a => V.innerInterCode P cons a acc m) 0 (decodeList n) := by
  have hf : (fun (acc x : ℕ) => V.outerInterStp P cons (Nat.pair x (Nat.pair acc m)))
      = (fun acc a => V.innerInterCode P cons a acc m) := by
    funext acc a; exact V.outerInterStp_eq P cons a acc m
  unfold interCode; rw [foldCode_eq', hf]

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
