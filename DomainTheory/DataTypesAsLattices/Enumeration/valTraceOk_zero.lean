/-ai
If m lies in the G combinator, then the one-entry trace with code zero, member m, and time stamp zero is well formed, and it records membership of m at code zero.

The only entry is that triple. Its code is zero, so the structural clause holds, and the hypothesis that m lies in the G combinator gives the G clause. The same triple is the recorded membership.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code









theorem valTraceOk_zero (m : ℕ) (hm : m ∈ Gcomb) :
    valTraceOk [(0, m, 0)] ∧ valTraceHas [(0, m, 0)] 0 m := by
  refine ⟨⟨?_, ?_⟩, ⟨0, by simp⟩⟩
  · intro e he
    simp at he
    subst e
    exact Or.inl rfl
  · intro e he he0
    simp at he
    subst e
    exact hm

end DomainTheory.DataTypesAsLattices
