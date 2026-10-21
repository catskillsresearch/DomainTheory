/-ai
The bit list of a natural number j is the list of those indices k at most j for which the k-th binary digit of j is set, obtained by filtering the initial range of length j + 1.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

def bitList (j : ℕ) : List ℕ :=
  (List.range (j + 1)).filter (fun k => j.testBit k)

end DomainTheory.DataTypesAsLattices
