/-ai
A set unequal to the empty set has a member.

If it had none, extensionality together with the characterization of membership in the empty set would force the set to be empty.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices































theorem exists_mem_of_ne_bot {x : Pomega} (h : x ≠ botElem) : ∃ m, m ∈ x := by
  by_contra hc
  refine h ?_
  ext n
  simp only [mem_botElem, iff_false]
  exact fun hn => hc ⟨n, hn⟩

end DomainTheory.DataTypesAsLattices
