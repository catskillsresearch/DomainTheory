module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Enumeration.applyNat
public import DomainTheory.DataTypesAsLattices.Enumeration.num
public import DomainTheory.DataTypesAsLattices.Enumeration.unionCode
public import DomainTheory.DataTypesAsLattices.Enumeration.botCode

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

noncomputable def finAux (j : ℕ) : ℕ → ℕ
  | 0 => botCode
  | k + 1 =>
      if j.testBit k then
        applyNat (applyNat unionCode (num k)) (finAux j k)
      else finAux j k

end DomainTheory.DataTypesAsLattices
