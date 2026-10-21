/-ai
Every finite set of natural numbers is recursively enumerable.

The proof is by induction on the finite set. The empty set is the bottom element, which is recursively enumerable. Inserting a number is the union of the singleton of that number with the remaining finite set, and both the singleton and the remaining set are recursively enumerable, so their union is.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
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
