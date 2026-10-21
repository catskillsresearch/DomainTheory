/-ai
The inner intersection code equals the left fold, along the decoded list of m, which prepends the intersection index of a and the current index to the accumulator when the consistency test of that pair returns one, and otherwise leaves the accumulator unchanged.

The inner step on the packed state agrees with that selection, by the inner-step equation. Unfolding the definition and rewriting by the fold-code equation therefore gives the left fold.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.innerInterStp
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.innerInterStp_eq
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.innerInterCode

@[expose] public section

set_option linter.unusedSectionVars false

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
