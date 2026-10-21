/-ai
The chain characteristic of a function-space code and a list code equals the left fold of the pure step, starting from the pairing of the master index with 1, along the decoded list.

Unfold the characteristic as a fold. The packed step agrees with the pure step, so the fold is the left fold of the pure step.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.fixStp_eq

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}






variable (P : ComputablePresentation V)






theorem fixChainChar_eq (fincl : ℕ → ℕ) (c i : ℕ) :
    fixChainChar P fincl c i
      = List.foldl (fixPStep fincl c) (Nat.pair P.masterIdx 1) (decodeList i) := by
  unfold fixChainChar
  rw [foldCode_eq']
  have hstep : (fun acc x => fixStp fincl (Nat.pair x (Nat.pair acc c))) = fixPStep fincl c := by
    funext acc x; exact fixStp_eq fincl c acc x
  rw [hstep]

end DomainTheory.NeighbourhoodSystems
