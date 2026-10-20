module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat_finAux

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

































































/-- **Scott 1976, before Theorem 3.5.** `val(fin j) = e j`. -/
theorem valNat_fin (j : ℕ) : valNat (fin j) = e j :=
  by
    rw [fin, valNat_finAux]
    ext n
    simp only [Set.mem_ofPred_eq, mem_e]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨Nat.lt_succ_of_le (mem_e_le (mem_e.mpr h)), h⟩

end DomainTheory.DataTypesAsLattices
