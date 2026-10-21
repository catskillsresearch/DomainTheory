/-ai
The auxiliary finAux j k scans the first k bits of j. At stage 0 it returns the bottom code. At stage k + 1, if bit k of j is set it applies the union code to the numeral of k and then to the value at stage k, and otherwise it returns the value at stage k.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.applyNat
public import DomainTheory.DataTypesAsLattices.Enumeration.num
public import DomainTheory.DataTypesAsLattices.Enumeration.unionCode
public import DomainTheory.DataTypesAsLattices.Enumeration.botCode

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- Primitive recursion scanning the first `k` bits of `j`. -/
noncomputable def finAux (j : ℕ) : ℕ → ℕ
  | 0 => botCode
  | k + 1 =>
      if j.testBit k then
        applyNat (applyNat unionCode (num k)) (finAux j k)
      else finAux j k

end DomainTheory.DataTypesAsLattices
