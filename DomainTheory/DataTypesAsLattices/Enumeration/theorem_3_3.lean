module

public import Mathlib.Computability.Halting
public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Enumeration.applyNat
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat
public import DomainTheory.DataTypesAsLattices.Enumeration.num
public import DomainTheory.DataTypesAsLattices.Enumeration.secondRecVal
public import DomainTheory.DataTypesAsLattices.Enumeration.secondRecOperator
public import DomainTheory.DataTypesAsLattices.Enumeration.secondRecV
public import DomainTheory.DataTypesAsLattices.Enumeration.recNat
public import DomainTheory.DataTypesAsLattices.Enumeration.recCode
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_secondRecV
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_recNat
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat_codes
public import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_12
public import DomainTheory.DataTypesAsLattices.Lambda.Ycomb
public import DomainTheory.DataTypesAsLattices.Lambda.Ycomb_more

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

namespace theorem_3_3

/-- **Scott 1976, Theorem 3.3 (iii)** from (i) and (ii):
`val(rec(n)) = val(n)(rec(n))`. -/
theorem from_v (v : ℕ → ℕ) (n : ℕ)
    (hv : valNat (v n) = secondRecVal (valNat n)) :
    valNat (recNat v n) = funOf (valNat n) (ofNat (recNat v n)) := by
  rw [recNat, valNat.app, hv, eq_3_12, secondRecVal.app]
  ext k
  constructor
  · intro hk
    obtain ⟨m, hm, hkm⟩ := Set.mem_iUnion₂.mp hk
    simp [ofNat] at hm; subst hm; exact hkm
  · intro hk
    exact Set.mem_iUnion₂.mpr ⟨v n, rfl, hk⟩

/-- **Scott 1976, Theorem 3.3 (i).** -/
theorem i (n : ℕ) :
    valNat (secondRecV n) = secondRecVal (valNat n) := by
  rw [secondRecV, valNat.app, valNat.secondRecOperatorCode_eq,
    secondRecOperator.app]

theorem ii (v : ℕ → ℕ) (n : ℕ) :
    recNat v n = applyNat (v n) (num (v n)) := rfl

theorem val (n : ℕ) :
    valNat (recCode n) = funOf (valNat n) (valNat (recCode n)) := by
  rw [recCode, valNat.app, valNat.Ycode_eq]
  exact Ycomb.unfold (valNat n)

end theorem_3_3

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
    theorem_3_3.i, theorem_3_3.ii secondRecV,
    fun n => theorem_3_3.from_v secondRecV n (theorem_3_3.i n)⟩

end DomainTheory.DataTypesAsLattices
