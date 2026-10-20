module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.theorem_3_4_diagonal
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_diagonalInterCode
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat_diagonalInterCode

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices
























































/-- **Scott 1976, Theorem 3.4 (The incompleteness theorem).**
The set of Gödel numbers denoting bottom is not recursively enumerable. -/
theorem theorem_3_4 :
    ¬ IsRE {n | valNat n = botElem} := by
  intro hb
  have hpre : IsRE {i | diagonalInterCode i ∈ {n | valNat n = botElem}} :=
    hb.comp primrec_diagonalInterCode.to_comp
  obtain ⟨k, hk⟩ :=
    theorem_3_2_surjective (IsRE.combinatory hpre)
  exact theorem_3_4_diagonal (val := valNat) (v := diagonalInterCode)
    valNat_diagonalInterCode rfl ⟨k, hk⟩


end DomainTheory.DataTypesAsLattices
