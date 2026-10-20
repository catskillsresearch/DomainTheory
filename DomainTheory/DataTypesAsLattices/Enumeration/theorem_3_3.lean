module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_secondRecV
public import DomainTheory.DataTypesAsLattices.Enumeration.theorem_3_3_i
public import DomainTheory.DataTypesAsLattices.Enumeration.theorem_3_3_ii
public import DomainTheory.DataTypesAsLattices.Enumeration.theorem_3_3_from_v
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_recNat

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

















































/-- **Scott 1976, Theorem 3.3 (The second recursion theorem).**
The functions `v` and `rec` are primitive recursive and satisfy clauses
(i)--(iii) of the paper. -/
theorem theorem_3_3 :
    ∃ v : ℕ → ℕ, Primrec v ∧
      Primrec (recNat v) ∧
      (∀ n, valNat (v n) = secondRecVal (valNat n)) ∧
      (∀ n, recNat v n = applyNat (v n) (num (v n))) ∧
      ∀ n, valNat (recNat v n) =
        funOf (valNat n) (ofNat (recNat v n)) :=
  ⟨secondRecV, primrec_secondRecV, primrec_recNat secondRecV primrec_secondRecV,
    theorem_3_3_i, theorem_3_3_ii secondRecV,
    fun n => theorem_3_3_from_v secondRecV n (theorem_3_3_i n)⟩

end DomainTheory.DataTypesAsLattices
