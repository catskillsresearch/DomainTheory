/-ai
The bottom term avoids every index i.

Unfold the term. For each of the two identical subterms, either the bound index 9 equals i, giving the left avoidance disjunct, or both occurrences of 9 differ from i, giving the right avoidance disjunct.
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


theorem enumBottomTerm_avoids (i : ℕ) : enumBottomTerm.Avoids i := by
  unfold enumBottomTerm
  constructor <;>
    (by_cases h : 9 = i
     · exact Or.inl h
     · exact Or.inr ⟨h, h⟩)

end DomainTheory.DataTypesAsLattices
