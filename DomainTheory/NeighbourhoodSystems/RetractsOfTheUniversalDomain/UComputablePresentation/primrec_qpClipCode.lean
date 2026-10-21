/-ai
The clip code is primitive recursive.

The two components of a pair code are primitive recursive, and pairing the rational maximum of the first with the code of zero and the rational minimum of the second with the code of one equals the clip code.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.qpClipCode

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem primrec_qpClipCode : Nat.Primrec qpClipCode := by
  have h1 : Nat.Primrec (fun e : ℕ => e.unpair.1) := Nat.Primrec.left
  have h2 : Nat.Primrec (fun e : ℕ => e.unpair.2) := Nat.Primrec.right
  exact ((primrec_ratMaxCode.comp (h1.pair (Nat.Primrec.const zeroCode))).pair
    (primrec_ratMinCode.comp (h2.pair (Nat.Primrec.const oneCode)))).of_eq fun _ => rfl

end DomainTheory.NeighbourhoodSystems
