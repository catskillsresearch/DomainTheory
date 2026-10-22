module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2ebot
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2enumeral
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2eunion

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


theorem IsRE.ofFinset (s : Finset ℕ) : IsRE (s : Set ℕ) := by
  induction s using Finset.induction with
  | empty =>
    simpa [botElem] using IsRE.bot
  | insert k s _hk ih =>
    have h : (insert k s : Set ℕ) = ofNat k ∪ (s : Set ℕ) := by
      ext; simp [ofNat]
    simpa [h] using IsRE.union (IsRE.numeral k) ih

end DomainTheory.DataTypesAsLattices
